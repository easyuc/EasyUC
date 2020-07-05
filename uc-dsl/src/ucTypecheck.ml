open EcLocation
open UcParseTree
open UcParser
open UcTypes
open UcEcTypes
open UcTypechecked
open UcUtils

(*circular references*)

let refsRefs (getRefs: string -> IdSet.t)  (refs:IdSet.t) : IdSet.t =
	let addRefs elt set = IdSet.union (getRefs elt) set in
	IdSet.fold addRefs refs IdSet.empty

let getDependencies (getRefs: string -> IdSet.t) (id:string)  =
	let rec tc refs = 
		let refs' = refsRefs getRefs refs in
		if IdSet.subset refs' refs then refs
		else tc (IdSet.union refs' refs)
	in tc (getRefs id)

let checkCircRefs (getRefs:('o located) IdMap.t-> string -> IdSet.t) (os:('o located) IdMap.t) : unit =
	let deps = IdMap.mapi (fun id o -> getDependencies (getRefs os) id) os in
	let circ = IdMap.filter (fun id rs -> IdSet.exists (fun r -> r=id) rs) deps in
	if IdMap.is_empty circ then ()
	else let id = fst (IdMap.choose circ) in let lid = loc (IdMap.find id os) in
		parse_error lid (Some(id^" contains a circular reference."))

(*-------------------*)

(*Convert a list from dlParseTree to IdMap*)

let checkUniqueId (al: 'a list) (getId: 'a -> id) : 'a IdMap.t =
	let idMap = IdMap.empty in
	List.fold_left 
		(fun idMap a -> 
		let idL = getId a in 
		if existsId idMap (unloc idL) then 
		  parse_error (loc idL) (Some ("Duplicate identifier: "^(unloc idL)))
		else
		  IdMap.add (unloc idL) a idMap
		)
		idMap al

(*----------------------------------------*)



(*EC type checks*)



let checkParams (nTl:nameType list) : typC IdMap.t =
		let ntMap = checkUniqueId nTl (fun nt -> nt.id) in
		IdMap.map (fun (nt:nameType) -> mk_loc (loc nt.id) ((checkType nt.ty), (index nt nTl))) ntMap





(*--------------*)



(*IO checks*)
let checkExistsIO (ermsgpref: string) (eIO:string->bool) (ioI:ioItem) : ioItemC =
		let uid = unloc ioI.ioId in
		if eIO uid
		then mk_loc (loc ioI.id) ioI.ioId
		else parse_error (loc ioI.ioId) (Some (ermsgpref^" "^uid^" hasn't been defined yet."))

let checkCompIoBody (ermsgpref: string) (eIO: string->bool) (iob:compositeIObody) : ioBodyC =
	let ioItemMap = checkUniqueId iob (fun ioI -> ioI.id)  in
	Composite (IdMap.map (checkExistsIO ermsgpref eIO) ioItemMap)


let checkBasicIoBody (biob:basicIObody) : ioBodyC =
		let msgMap = checkUniqueId biob (fun md -> md.id) in
Basic (IdMap.map (fun (md:messageDef) ->mk_loc (loc md.id) {direction = md.direction; content = (checkParams md.content); portLabel = md.portLabel}) msgMap)

let checkCompositesRefBasics (ios:ioC IdMap.t) =
	let (composites, basics) = 
		IdMap.partition (fun id ioc -> match (unloc ioc) with Composite x->true |_->false) ios in
	let ebIO = existsId basics in
	IdMap.iter (fun id ioc -> 
	match (unloc ioc) with Composite its -> IdMap.iter (fun id idl -> 
		let uid = unloc (unloc idl) in
		if (ebIO uid) then ()
		else parse_error (loc (unloc idl)) (Some (uid^" is not a basic IO."))
	) its |_->()) composites


let checkADIOs (errmsgpref:string) (adIOMap: io IdMap.t) =
	let eIO = existsId adIOMap in
	let checkADIODef (io:io) : ioC = 
		match io.body with
		| Basic iob -> mk_loc (loc io.id) (checkBasicIoBody iob)
		| Composite iob -> mk_loc (loc io.id) (checkCompIoBody errmsgpref eIO iob)
	in
	let adIOs = IdMap.map checkADIODef adIOMap in
	checkCompositesRefBasics adIOs;
	adIOs

let checkDirIOs (dirIOMap: io IdMap.t) = checkADIOs "directIO" dirIOMap

let checkAdvIOs (advIOMap: io IdMap.t) = checkADIOs "adversarialIO" advIOMap
		
(*---------*)

(*Real Functionality checks*)

let checkIsComposite (ios: ioC IdMap.t) (id:id) : unit =
	let uid= unloc id in
	match unloc (IdMap.find uid ios) with
	| Basic io -> parse_error (loc id) (Some("The IO must be composite (even if it has only one component)."))
	| Composite io -> ()

let checkRealFunParams (dirIOs:ioC IdMap.t) (params:funParam list) : (ioItemC * int) IdMap.t =
	let checkRealFunParam (dirIOs:ioC IdMap.t) (param:funParam) : (ioItemC * int) =
		let dirIOid = unloc param.idDirIO in
		if not (existsId dirIOs dirIOid) then parse_error (loc param.idDirIO) (Some("directIO "^dirIOid^" doesn't exist."))
		else checkIsComposite dirIOs param.idDirIO;
		((mk_loc (loc param.id) param.idDirIO), (index param params))
	in
	let paramMap = checkUniqueId params (fun p->p.id) in
	IdMap.map (checkRealFunParam dirIOs) paramMap

let checkSubFunDecl (eFId:string->bool) (eParam:string->bool) (eSFId:string->bool)(sf:subFunDecl) : subFunDeclC =
	let funId = unloc sf.funId in
	if (eFId funId) then
		(
		List.iter (fun p ->let up=unloc p in if (eParam up) || (eSFId up) then () else parse_error (loc p) (Some("Parameters to subfunctionalities can be either parameters of functionality or other subfunctionalities. "^up^" is neither.")) ) sf.funParamIds
		)
	else parse_error (loc sf.funId) (Some("Nonexisting functionality : "^funId))
	;
	mk_loc (loc sf.id) {funId=funId; funParamIds=sf.funParamIds}



let checkExactlyOneInitialState (id:id) (sds:stateDef list) : id =
	let inits = List.filter (fun sd -> match sd with InitialState s ->true | _ -> false ) sds in
	match List.length inits with
	| 0 -> parse_error (loc id) (Some((unloc id)^" doesn't have initial state"))
	| 1 -> (match List.hd inits with | InitialState s -> s.id | FollowingState s -> raise (Failure "impossible, list contains only InitialState"))
	| _ -> parse_error (loc id) (Some((unloc id)^" has more than one initial state"))

let checkStateDecl (initId:id) (s:state) : stateC =
	let isInitial = (initId=s.id) in
	let params = checkParams s.params in
	let vars = IdMap.map (fun tip -> mk_loc (loc tip) (fst (unloc tip))) (checkParams s.code.vars) in
	let dup = IdMap.find_first_opt (fun id -> IdMap.mem id vars) params in
	match dup with
	| None -> mk_loc (loc s.id) {isInitial=isInitial; params=params; vars=vars; mmcodes=s.code.mmcodes}
	| Some (id,t) -> parse_error (loc t) (Some("Variable name "^id^" is the same as one of the states parameters."))
			
let dropStateCtor (sd:stateDef) : state =
	match sd with 
	| InitialState s   -> s
	| FollowingState s -> s

let checkStates (id:id) (code:stateDef list) : stateC IdMap.t =
	let initId = checkExactlyOneInitialState id code in
	let states = List.map (fun sd -> dropStateCtor sd) code in
	let codeMap = checkUniqueId states (fun s->s.id) in
	IdMap.map (checkStateDecl initId) codeMap 

type bIOPath =  (string list) * basicIObodyC

type rFbIOPaths = {direct:bIOPath list; adversarial:bIOPath list; internal:bIOPath list }

let getbIOPaths (root:string) (ioid:string) (ios:ioC IdMap.t) : bIOPath list =
	let getbBody (id:string) : basicIObodyC =
		let io = IdMap.find id ios in
		match (unloc io) with
		| Basic b -> b
		| _ -> raise (Failure "Cannot happen, this function is called only on Basic IOs")
	in
	let io = IdMap.find ioid ios in
	match (unloc io) with
	| Basic b -> [([root],b)]
	| Composite cio -> IdMap.fold (fun id it l-> ([root;id],getbBody (unloc (unloc it)))::l) cio []

let getIOPaths (ioid:string) (ios:ioC IdMap.t) : string list list =
	let bps = getbIOPaths ioid ioid ios in
	List.map (fun bp -> fst bp) bps

let getFunIOPaths (idDirIO:string) (idAdvIO:string option) (dirIOs:ioC IdMap.t) (advIOs:ioC IdMap.t) : string list list =
	let dir = getIOPaths idDirIO dirIOs in
	let adv = match idAdvIO with
		  | Some id -> getIOPaths id advIOs
		  | None -> []
	in dir@adv

let checkIOpath (idDirIO:string) (idAdvIO:string option) (dirIOs:ioC IdMap.t) (advIOs:ioC IdMap.t) (iop: id list) : string list located =
	let uiop = unlocs iop in
	let loc = mergelocs iop in
	let ps = getFunIOPaths idDirIO idAdvIO dirIOs advIOs in
	if (List.mem uiop ps) then mk_loc loc uiop else
	let psf = List.filter (fun p -> (List.tl p) = uiop) ps in
	match (List.length psf) with
	| 0 -> parse_error loc (Some ((string_of_IOpath uiop)^" is not a part of the interfaces implemented by functionality."))
	| 1 -> mk_loc loc (List.hd psf)
	| _ -> parse_error loc (Some ((string_of_IOpath uiop)^" is ambiguous, it is in both direct and adversarial IOs implemented by functionality."))	

let checkServedPaths (serves:string list located list) (idDirIO:string) (pid:id): unit =
	let er = "A party can serve at most one basic direct IO and one basic adversarial IO." in
	let erone ="A party must serve one basic direct IO." in
	match (List.length serves) with
	| 0 -> parse_error (loc pid) (Some erone)
	| 1 -> if (List.hd (unloc (List.nth serves 0)))=idDirIO
		then () else parse_error (loc (List.nth serves 0)) (Some erone)
	| 2 -> if (List.hd (unloc (List.nth serves 0)))<>(List.hd (unloc (List.nth serves 1)))
		then () else parse_error (loc (List.nth serves 1)) (Some er)
	| _ -> parse_error (mergelocs serves) (Some er)
		
let checkIOsUnique (iops: string list located list) : unit =
	ignore (List.fold_left (fun l iop ->
		let uiop = unloc iop in
		if List.mem uiop l then parse_error (loc iop) (Some ("Parties must serve distinct IOs"))
		else uiop::l
	) [] iops)

let checkIOsCover (idDirIO:string) (idAdvIO:string option) (dirIOs:ioC IdMap.t) (advIOs:ioC IdMap.t) (servedPs: string list located list): unit =
	let serps = unlocs servedPs in
	let ps = getFunIOPaths idDirIO idAdvIO dirIOs advIOs in
	let unserved = List.filter (fun p -> not (List.mem p serps)) ps	in
	if (List.length unserved)=0 then () else
	parse_error (mergelocs servedPs) (Some ("These IOs are not served by any party: "^(string_of_IOpaths unserved)))

let checkPartyDecl (idDirIO:string) (idAdvIO:string option) (dirIOs:ioC IdMap.t) (advIOs:ioC IdMap.t)(p:partyDef) : partyDefC =
	let serves = List.map (checkIOpath idDirIO idAdvIO dirIOs advIOs) p.serves in
	checkServedPaths serves idDirIO p.id;
	let code = checkStates p.id p.code in
	mk_loc (loc p.id) {serves=serves; code=code} 

let checkPartiesServeDirectSum (parties:partyDefC IdMap.t) (idDirIO:string) (idAdvIO:string option) (dirIOs:ioC IdMap.t) (advIOs:ioC IdMap.t): unit =
	let servedPs = IdMap.fold (fun id p l -> l@(unloc p).serves) parties [] in
	checkIOsUnique servedPs;	
	checkIOsCover idDirIO idAdvIO dirIOs advIOs servedPs

let getRealFunSubItemId (si:subItem) : id =
	match si with
	| SubFunDecl sf -> sf.id
	| PartyDef p -> p.id

let checkExistsDirIO (dirIOs:ioC IdMap.t) (idDirIO:id) =
	let uidDirIO = unloc idDirIO in
	if existsId dirIOs uidDirIO then () 
	else parse_error (loc idDirIO) (Some("directIO "^uidDirIO^" doesn't exist."))

let checkExistsI2SIO (i2sIOs:ioC IdMap.t) (idI2SIO:id) =
	let uidI2SIO= unloc idI2SIO in
	if existsId i2sIOs uidI2SIO then
		match unloc (IdMap.find uidI2SIO i2sIOs) with
		| Basic io -> ()
		| Composite io -> parse_error (loc idI2SIO) (Some("This adversarialIO cannot be composite."))
	else parse_error (loc idI2SIO) (Some("adversarialIO "^uidI2SIO^" doesn't exist."))


let checkFunDecl (eFId:string->bool) (dirIOs:ioC IdMap.t) (advIOs:ioC IdMap.t) (rFun:funDef) : funC =
	let params = checkRealFunParams dirIOs rFun.params in 
	checkExistsDirIO dirIOs rFun.idDirIO;
	let idDirIO = unloc rFun.idDirIO in 
	let idAdvIO = match rFun.idAdvIO with
			| None -> None
			| Some id -> 
				(
		let uid = unloc id in
		if existsId advIOs uid then Some uid
		else parse_error (loc id) (Some("adversarialIO "^uid^" doesn't exist."))
				) in
	let subItems = checkUniqueId rFun.body getRealFunSubItemId in
		(
		 let dupIds = IdMap.filter (fun id sf -> IdMap.mem id params) subItems in
		 if IdMap.is_empty dupIds then ()
		 else let id,dup = IdMap.choose dupIds in let lc=loc (getRealFunSubItemId dup) in
		 parse_error lc (Some("The name "^id^" is the same name as one of the functionalities parameters."))
		);
	let sfMap = filterMap (fun subI -> match subI with SubFunDecl sf ->Some sf | _->None) subItems in
	let eParam = existsId params and eSFId = existsId sfMap in
	let subFuns = IdMap.map (checkSubFunDecl eFId eParam eSFId) sfMap in
	let parties,states =
		checkIsComposite dirIOs rFun.idDirIO;
		if rFun.stateBody=[] then(			
			(match rFun.idAdvIO with Some id -> checkIsComposite advIOs id|_->());
			let pMap = filterMap (fun subI -> match subI with PartyDef p ->Some p | _->None) subItems in
			let ps = IdMap.map (checkPartyDecl idDirIO idAdvIO dirIOs advIOs) pMap in
			checkPartiesServeDirectSum ps idDirIO idAdvIO dirIOs advIOs;
			(ps,IdMap.empty))
		else
			let ss = checkStates rFun.id rFun.stateBody in
			(match rFun.idAdvIO with
			| None -> parse_error (loc rFun.id) (Some("A functionality with no parties must implement a basic adversarial interface"))
			| Some id -> checkExistsI2SIO advIOs id
			);
			(IdMap.empty,ss)
	in
	mk_loc (loc rFun.id) {params=params; idDirIO=idDirIO; idAdvIO=idAdvIO; subFuns=subFuns; parties=parties; states=states}

let getDirIOIdImplByFun (fid:string) (funs:funC IdMap.t) : string =
			let rF=IdMap.find fid funs in (unloc rF).idDirIO
			

let getParamDirIOIds (rFuns:funC IdMap.t) (rfid:string) :string list = 
	unlocs (unlocs (toList((unloc (IdMap.find rfid rFuns)).params)))

let checkSubFunParams (funs:funC IdMap.t) : unit =
	let getDirIOId rfid id =		
		let f = unloc (IdMap.find rfid funs) in
		let p = IdMap.find_opt id f.params in
		let s = IdMap.find_opt id f.subFuns in
			match (p,s) with
			| (Some pm, None) -> unloc (unloc (fst pm))
			| (None, Some sf) -> getDirIOIdImplByFun ((unloc sf).funId) funs
			| _ -> raise (Failure "Impossible - we already checked that subFun params exist and are unique in checkSubFunDecl")
	in
	let getDirIOIds rfid ids = List.map (fun id -> getDirIOId rfid id) ids in
	let checkSFPs rfid sf =
		let usf = unloc sf in
		let sfps = getParamDirIOIds funs usf.funId in
		let sfpids = unlocs usf.funParamIds in
		let sfps'= getDirIOIds rfid sfpids in
		if (List.length sfps)<>(List.length sfps') then parse_error (loc sf) (Some("Wrong number of parameters for subfunctionality")) else
		if sfps<>sfps' then parse_error (loc sf) (Some("Parameter provided to subfunctionality implement different directIOs from declared parameters.")) else
		true
	in
	ignore (IdMap.for_all 
		(fun idrf rf -> IdMap.for_all 
			(fun id sf -> checkSFPs idrf sf) (unloc rf).subFuns
		) funs)

type stateVars = {flags:string list; internalPorts:QidSet.t; consts:typ IdMap.t; vars:typ IdMap.t; initializedVs:IdSet.t}

let initStateVars (s:stateBody) (ports: QidSet.t) (flags:string list): stateVars =
	let consts = IdMap.map (fun p -> fst (unloc p)) s.params in
	let vars = IdMap.map (fun v -> unloc v) s.vars in
	{flags=flags; internalPorts=ports; consts=consts; vars=vars; initializedVs=IdSet.empty}

type stateSig = typ list option

let getStateSig (s:stateBody) : stateSig =
	if s.isInitial then None
	else
	let ps = IdMap.bindings s.params in
	let ts = unlocs (snd (List.split ps)) in
	let tord = List.sort (fun t1 t2-> (snd t1)-(snd t2)) ts in
	Some (fst (List.split tord))

let getStateSigs (states:stateC IdMap.t) : stateSig IdMap.t =
	IdMap.map (fun s-> getStateSig (unloc s) ) states

let string_of_msgPath (mp:msgPath) : string =
	let siop = string_of_IOpath (unlocs mp.ioPath) in
	match mp.msgType with 
	| MsgType id -> siop^"."^(unloc id)
	| OtherMsg l -> siop^".othermsg"

let string_of_msgPathl (mpl: msgPath list) : string=
	string_of_stringl (List.map (fun mp->string_of_msgPath mp) mpl)

let filterbIOPs (dir:msgInOut) (biops:bIOPath list) : bIOPath list =
	List.map (fun biop -> ((fst biop),IdMap.filter(fun id md -> (unloc md).direction=dir)(snd biop))) biops
	

let getIncomingMsgPaths (bps:rFbIOPaths) : rFbIOPaths =
	{
		direct = filterbIOPs In bps.direct;
		adversarial = filterbIOPs In bps.adversarial;
		internal = filterbIOPs Out bps.internal
	}

let getOutgoingMsgPaths (bps:rFbIOPaths) : rFbIOPaths =
	{
		direct = filterbIOPs Out bps.direct;
		adversarial = filterbIOPs Out bps.adversarial;
		internal = filterbIOPs In bps.internal
	}

let msgLoc (mp:msgPath) : EcLocation.t =
	match mp.msgType with
	| MsgType id -> loc id
	| OtherMsg l -> l

let msgPaths_of_bIOPath (bp:bIOPath) : msgPath list =	
IdMap.fold (fun id bod l -> { ioPath=dummylocl (fst bp); msgType=MsgType (dummyloc id) }::l ) (snd bp) []

let mp_of_bpl (bpl:bIOPath list) : msgPath list =
		List.flatten (List.map (fun bp -> msgPaths_of_bIOPath bp) bpl)

let flatten_rFbIOPaths (bps:rFbIOPaths) : bIOPath list =
	bps.direct@bps.adversarial@bps.internal

let msgPaths_of_rFbIOPaths (bps:rFbIOPaths) : msgPath list =
	mp_of_bpl (flatten_rFbIOPaths bps)

let checkMsgPath (bps:rFbIOPaths) (mp:msgPath) : msgPath =
	let ips = mp_of_bpl bps.internal in
	let allps = msgPaths_of_rFbIOPaths bps in	
	let filterByMsgType (mt:id) (mpl:msgPath list) : msgPath list =
		List.filter (fun p-> match p.msgType with MsgType mt' -> (unloc mt')=(unloc mt) | _->false) mpl
	in
	let filterByPortNameMsgType (pt:id) (mt:id) (mpl:msgPath list) : msgPath list =
filterByMsgType mt (List.filter (fun p-> (unloc (List.hd(List.rev p.ioPath)))=(unloc pt)) mpl)
	in
	let unexpected() = 
		parse_error (msgLoc mp) (Some("The message is unexpected. These messages are expected:"^(string_of_msgPathl allps))) 
	in
	let ambiguous (mtch:msgPath list) =
		parse_error (msgLoc mp) (Some("The message is ambiguous. There are multiple messages that match the description:"^(string_of_msgPathl mtch)))
	in
	let filtered (mtch:msgPath list) (imtch:msgPath list) : msgPath =
		match (List.length mtch) with
		| 0 -> unexpected()
		| 1 ->	let l = merge (mergelocs mp.ioPath) (msgLoc mp) in
			if imtch=[] then 
			let ret=List.hd mtch in {ioPath = List.map (fun id -> mk_loc l (unloc id)) ret.ioPath; msgType = mp.msgType }
			else parse_error l (Some ("Internal messages must have full paths. Did you mean "^(string_of_msgPath (List.hd mtch))^" ?"))
		| _ -> ambiguous mtch
	in
	match mp.msgType with
	| MsgType mt ->
		(
		if (List.exists (fun p -> (string_of_msgPath p)=(string_of_msgPath mp)) allps) then mp
		else
		match (List.length mp.ioPath) with
		| 0 ->	let filter = filterByMsgType mt in
			let mtch = filter allps in
			let imtch = filter ips in
			filtered mtch imtch
		| 1 ->	let filter = filterByPortNameMsgType (List.hd mp.ioPath) mt in
			let mtch = filter allps in
			let imtch = filter ips in
			filtered mtch imtch
		| _ ->  unexpected()
		)
	| OtherMsg l -> if (List.exists (fun p-> qid1_starts_with_qid2 p.ioPath mp.ioPath) allps) then mp else unexpected()

let removeCoveredPaths (mps:msgPath list) (mp:msgPath) : msgPath list =
	let covered mp1 mp2 =
		match mp2.msgType with
		| MsgType mt -> ((string_of_msgPath mp1)=(string_of_msgPath mp2))
		| OtherMsg l -> qid1_starts_with_qid2 mp1.ioPath mp2.ioPath
	in
  	let rem = List.filter (fun mp' -> not (covered mp' mp) ) mps in
	if (List.length mps)=(List.length rem)
	then parse_error (msgLoc mp) (Some("This match is covered by previous matches and would never execute."))
	else rem

let msgPaths_of_rFbIOPaths_w_othermsg (bps:rFbIOPaths) : msgPath list =
	let mps = msgPaths_of_rFbIOPaths bps in
	let omps = List.map (fun bp -> { ioPath=dummylocl (fst bp); msgType=OtherMsg _dummy }) (flatten_rFbIOPaths bps) in
	mps@omps

let checkMMDsNonEmpty (bps:rFbIOPaths) (mpl:msgPath list) : msgPath list =
	let mps = msgPaths_of_rFbIOPaths_w_othermsg bps in
	List.fold_left (fun mps mp -> removeCoveredPaths mps mp) mps mpl


let checkMsgMatchDeltas (rfbps:rFbIOPaths) (mml:msgMatch list) : unit =
	let mps = getIncomingMsgPaths rfbps in
	let r = checkMMDsNonEmpty mps (List.map (fun (mm:msgMatch) -> mm.path) mml) in
	if r<>[] then
		let l = msgLoc ((List.hd (List.rev mml)).path)
		in parse_error l (Some("Message match is not exhaustive, these messages are not matched:"^(string_of_msgPathl r)))
	else ()

let checkTypesCompatible (vid:id) (vt:typ) (typ:typ) : unit=
	if not (vt=typ)
	then parse_error (loc vid) (Some((unloc vid)^" doesn't have type compatible with "^(string_of_typ typ)))

let getDeclaredConstVars (sv:stateVars)=
	IdMap.union (fun id p1 p2 ->raise (Failure "Impossible, we already checked params and local vars have different ids")) sv.consts sv.vars

let checkExistsAndHasCompatibleType (vid:id) (typ:typ) (sv:stateVars) : unit =
	let uvid = unloc vid in
	let pvs = getDeclaredConstVars sv in
	if not (IdMap.mem uvid pvs)
	then parse_error (loc vid) (Some(uvid^" is neither a local variable nor a state parameter"));
	let vt = IdMap.find uvid pvs in
	checkTypesCompatible vid vt typ
	
let checkAddBinding (vid:id) (sv:stateVars) : stateVars =
	let uvid = unloc vid in
	if not (IdMap.mem uvid sv.vars)
	then parse_error (loc vid) (Some(uvid^" is not a local variable and values cannot be bound to it."))
	else
	{flags=sv.flags; internalPorts=sv.internalPorts; consts=sv.consts;vars=sv.vars;initializedVs=(IdSet.add uvid sv.initializedVs)}

let checkTypeAddBinding (vid:id) (typ:typ) (sv:stateVars) : stateVars =
	checkExistsAndHasCompatibleType vid typ sv;
	checkAddBinding vid sv

let checkAddConst (cid:id) (ct:typ) (valt:typ) (sv:stateVars) : stateVars =
	checkTypesCompatible cid ct valt;
	let ucid = unloc cid in
	let pvs = getDeclaredConstVars sv in
	if (IdMap.mem ucid pvs)
	then parse_error (loc cid) (Some(ucid^" is already used."))
	else {flags=sv.flags; internalPorts=sv.internalPorts; consts=IdMap.add ucid ct sv.consts;vars=sv.vars;initializedVs=sv.initializedVs}

let checkPortVarBinding (bps:rFbIOPaths) (mp:string list) (vid:id) (sv:stateVars) : stateVars =
	let d = List.exists (fun bp -> sl1_starts_with_sl2 (fst bp) mp) bps.direct
	and i = List.exists (fun bp -> sl1_starts_with_sl2 (fst bp) mp) bps.internal
	and a = List.exists (fun bp -> sl1_starts_with_sl2 (fst bp) mp) bps.adversarial
	in
	if not (d && not i && not a)
	then parse_error (loc vid) (Some("The message "^(string_of_IOpath mp)^" maybe isn't an incoming message of a directIO served by the party and cannot bind the source port to a variable."))
	else
	checkAddConst vid portType portType sv

let checkItemTypeAddBinding (sv:stateVars) (mi:matchItem) (typ:typ) : stateVars =
	match mi with
	| Wildcard l -> sv
	| Const id -> checkAddConst id typ typ sv
	| ConstType nt -> checkAddConst nt.id (checkType nt.ty) typ sv

let rec getLocTy (ty:ty) : EcLocation.t =
	match ty with
	| NamedTy id -> loc id
	| TupleTy tl -> mergeall (List.map (fun t -> getLocTy t) tl)

let getLocMatchItem (mI: matchItem) : EcLocation.t =
	match mI with
	| Wildcard l -> l
	| Const id -> loc id
	| ConstType nt -> merge (loc nt.id) (getLocTy nt.ty)

let getLocMatchItemList (tm:matchItem list) : EcLocation.t = mergeall (List.map (fun mi ->getLocMatchItem mi) tm)

let checkMsgContentBindings (ps:bIOPath list) (mp:string list*string) (tm:matchItem list) (sv:stateVars) : stateVars =
	let p = List.find (fun p-> (fst p) = (fst mp)) ps in
	let mt = toList (unlocm((unloc(IdMap.find (snd mp) (snd p))).content)) in
	if (List.length mt)<>(List.length tm)
	then parse_error (getLocMatchItemList tm) (Some("The number of bindings is different then the number of message parameters."))
	else
	List.fold_left2 checkItemTypeAddBinding sv tm mt

let checkTupleMatch (bps:bIOPath list) (mm:msgMatch) (sv:stateVars) : stateVars =
	match mm.tupleMatch with
	| None -> sv
	| Some mil ->
		match mm.path.msgType with
		| OtherMsg l-> parse_error l (Some("othermsg cannot have value bindings. Do you have redundant parenthesis?"))
		| MsgType id -> checkMsgContentBindings bps ((unlocs mm.path.ioPath),(unloc id)) mil sv

let checkMatchBindings (bps:rFbIOPaths) (mm:msgMatch) (sv:stateVars) : stateVars =
	let sv'=	
		match mm.portVar with
		| Some id -> checkPortVarBinding bps (unlocs mm.path.ioPath) id sv
		| None -> sv
	in
	let ps = bps.direct@bps.adversarial@bps.internal in
	checkTupleMatch ps mm sv'

let getVarType (sv: stateVars) (id:id) : typ =
	let vs = IdMap.union (fun a1 a2 -> raise (Failure "Impossible! we already checked that params and vars have different names")) sv.consts sv.vars in
	IdMap.find (unloc id) vs

let checkInitialized (sv: stateVars) (id:id) : unit =
	let uid = unloc id in
	if (IdMap.mem uid sv.consts)||(IdSet.mem uid sv.initializedVs) then ()
	else parse_error (loc id) (Some(uid^" is not initialized."))	

let checkExprVar (sv: stateVars) (id:id) : typ =
	let r = getVarType sv id in
	checkInitialized sv id;
	r

let checkIsInternalPort (sv: stateVars) (qid:qid) : bool = QidSet.mem (unlocs qid) sv.internalPorts

let checkQidType (sv:stateVars) (qid:qid) : typ =
	try (
		match qid with
		| id::[] -> checkExprVar sv id
		| _ -> raise Not_found
    	)
	with Not_found -> 
		if (checkIsInternalPort sv qid) then portType else raise Not_found

let checkExpression (sv:stateVars) (expr:expressionL) : typ =
	UcExpressions.checkExpression (checkQidType sv) expr

let checkValAssign (sv:stateVars) (vid:id) (ex:expressionL) : stateVars =
	let etyp = checkExpression sv ex in
	checkTypeAddBinding vid etyp sv

let checkSamplAssign (sv:stateVars) (vid:id) (ex:expressionL) : stateVars =
	let etyp = checkExpression sv ex in
	if not (UcExpressions.isDistribution etyp) then parse_error (loc ex) (Some("You can sample only from distributions."))
	else
	let dtyp = UcExpressions.getDistrubutionTyp etyp  in 
	checkTypeAddBinding vid dtyp sv

let checkTransition (si:stateInstance) (ss:stateSig IdMap.t) (sv:stateVars) : unit =
	let ssig =
		try IdMap.find (unloc(si.id)) ss	
		with Not_found -> parse_error (loc si.id) (Some ("Non-existing state: "^(unloc si.id)))
	in
	match ssig, si.params with
	| None, None -> ()
	| None, Some params -> parse_error (loc si.id) (Some ("State doesn't have parameters, do you have reduntant parentheses?"))
	| Some sp, None ->  parse_error (loc si.id) (Some ("State has parameters, none are provided."))
	| Some sp, Some params ->
		if (List.length sp)<>(List.length params)
		then parse_error (loc si.id) (Some("Wrong number of parameters."))
		else
		let te = List.combine sp params in
		List.iteri (fun i (sigt,sip) ->
			let et = checkExpression sv sip in
			if (sigt <> et)&&(sigt<>univType)
			then parse_error (loc sip) (Some ((string_of_int (i+1))^". parameter of state "^(unloc si.id)^" has type "^(string_of_typ sigt)^", which is incompatible with provided type "^(string_of_typ et)))
			else ()
		   ) te

let checkMsgContentValues (es:expressionL list) (mc:typC IdMap.t) (sv:stateVars): unit =
	let sg = toList (unlocm mc) in
	let esl = mergelocs es in
	if (List.length es)<>(List.length sg) then parse_error esl (Some("Parameter number mismatch."))
	else 
	List.iter2 (fun ex typ-> if not ((checkExpression sv ex)=typ) then parse_error (loc ex) (Some("Parameter type mismatch")) ) es sg

let checkSendDirect (msg:msgInstance) (mc:typC IdMap.t) (sv:stateVars) : unit =
	let l=msgLoc msg.path in
	(
	match msg.portVar with
	| Some p -> checkExistsAndHasCompatibleType p portType sv; checkInitialized sv p;
	| None -> parse_error l (Some("Missing destination port."))
	);
	checkMsgContentValues msg.tupleInstance mc sv

let checkSendAdversarial (msg:msgInstance) (mc:typC IdMap.t) (sv:stateVars) : unit =
	let l=msgLoc msg.path in
	(
	match msg.portVar with
	| Some p -> parse_error l (Some("Only direct messages can have destination port."))
	| None -> ()
	);
	checkMsgContentValues msg.tupleInstance mc sv

let checkSendInternal (msg:msgInstance) (mc:typC IdMap.t) (sv:stateVars) : unit =
	let l=msgLoc msg.path in
	(
	match msg.portVar with
	| Some p -> parse_error l (Some("Messages to subfunctionalities cannot have destination port."))
	| None -> ()
	);
	checkMsgContentValues msg.tupleInstance mc sv

let isMsgPathInbIOPaths (mp:msgPath) (bps:bIOPath list) : bool =
	let bpo = List.find_opt (fun bp -> (fst bp) = (unlocs mp.ioPath))bps in
	match bpo with
	| Some bp -> true
	| None -> false

let getMsgDefForMsgPath (mp:msgPath) (bs:bIOPath list) : messageDefBody =
	let iop = unlocs mp.ioPath in
	let bio = List.find (fun bp -> (fst bp)=iop) bs in
	let mt  = match mp.msgType with MsgType id -> unloc id | OtherMsg l-> raise (Failure "OtherMsg doesn't have definition in interface") in
	let mdb = IdMap.find mt (snd bio) in
	unloc mdb

let checkSendMsgPath (msg:msgInstance) (bps:rFbIOPaths) (sv:stateVars) : msgInstance =
	let ps = getOutgoingMsgPaths bps in
	let path'= checkMsgPath ps msg.path in
	let msg' = {path=path'; tupleInstance=msg.tupleInstance; portVar=msg.portVar} in
	if (List.mem "simulator" sv.flags)&&(msg.path<>msg'.path) then
		parse_error (msgLoc msg.path) (Some("Messages sent by simulator must have complete path, did you mean "^(string_of_msgPath msg'.path)^" ?"))
	else ();
	msg'
	

let checkSend (msg:msgInstance) (bps:rFbIOPaths) (sv:stateVars) : msgInstance =
	let msg' = checkSendMsgPath msg bps sv in
	let bs = bps.direct@bps.adversarial@bps.internal in
	let mdbc = (getMsgDefForMsgPath msg'.path bs).content in
	(
	match msg'.path with
	| ( _ as p) when isMsgPathInbIOPaths p bps.direct -> checkSendDirect msg' mdbc sv
	| ( _ as p) when isMsgPathInbIOPaths p bps.adversarial -> checkSendAdversarial msg' mdbc sv
	| ( _ as p) when isMsgPathInbIOPaths p bps.internal -> checkSendInternal msg' mdbc sv
	| _ -> raise (Failure "impossible - the path is always in one of direct|adversarial|internal ")
	);
	msg'

let checkSendAndTransition (bps:rFbIOPaths) (ss:stateSig IdMap.t) (sat:sendAndTransition) (sv:stateVars)  : instruction =
	let msg'= checkSend sat.msg bps sv in
	checkTransition sat.state ss sv;
	SendAndTransition {msg=msg'; state=sat.state}

let mergeStateVars (sv1:stateVars) (sv2:stateVars) : stateVars =
	{flags=sv1.flags; internalPorts=sv1.internalPorts; consts=sv1.consts; vars=sv1.vars; initializedVs=IdSet.inter sv1.initializedVs sv2.initializedVs}


let rec checkITE (bps:rFbIOPaths) (ss:stateSig IdMap.t) (sv:stateVars) (ex:expressionL) (tins:instructionL list) (eins:instructionL list option) : instruction*stateVars =
	if (checkExpression sv ex)<>boolType then parse_error (loc ex) (Some("The condition must be a boolean expression.")) 
	else
	let (tinsC,einsC,sv') = checkBranches bps ss sv tins eins in
	((ITE (ex, tinsC, einsC)), sv')

and

checkBranches (bps:rFbIOPaths) (ss:stateSig IdMap.t) (sv:stateVars) (tins:instructionL list) (eins:instructionL list option) : instructionL list * instructionL list option * stateVars =
	let (tinsC,tsv) = checkInstructions bps ss sv tins in
	let (einsC,esv) = match eins with			  
			  | Some is -> let (is',esv) = checkInstructions bps ss sv is
					in (Some is',esv)
			  | None -> (None,sv)
	in
	let sv' = mergeStateVars tsv esv in
	(tinsC,einsC,sv')

and	
checkDecode (bps:rFbIOPaths) (ss:stateSig IdMap.t) (sv:stateVars) (ex:expressionL) (ty:ty) (mIs: matchItem list) (okins:instructionL list) (erins:instructionL list) : instruction * stateVars =
	if (checkExpression sv ex) <> univType
	then parse_error (loc ex) (Some "Only expressions of univ type can be decoded.")
	else 
	let dt = match checkType ty with
		| Tconstr (x,y) -> [Tconstr (x,y)]
		| Ttuple  t -> t
		| _ -> raise (Failure "checkType is supposed to return only Tconstr or Ttuple.")
	in
	if (List.length mIs)<>(List.length dt) 
	then parse_error (getLocMatchItemList mIs) (Some("The number of bindings is different from the arity of decoded type."))
	else
	let sv' = List.fold_left2 checkItemTypeAddBinding sv mIs dt in
	let (okinsC,erinsC,sv'') = checkBranches bps ss sv' okins (Some erins) in
	(Decode (ex,ty,mIs,okinsC,(BatOption.get erinsC)),sv'')

and
checkInstruction (bps:rFbIOPaths) (ss:stateSig IdMap.t) (insv:instructionL list*stateVars)  (i:instructionL): instructionL list*stateVars =
	let ins=fst insv in
	let sv =snd insv in
	match (unloc i) with
	| Assign (vid,ex) -> (ins@[i]),(checkValAssign sv vid ex)
	| Sample (vid,ex) -> (ins@[i]),(checkSamplAssign sv vid ex)
	| ITE (ex,tins,eins) -> let (iteC,sv') = checkITE bps ss sv ex tins eins in
				(ins@[mk_loc (loc i) iteC],sv')
	| Decode (ex,ty,mIs,okins,erins) -> let (matchC,sv') = checkDecode bps ss sv ex ty mIs okins erins in
				(ins@[mk_loc (loc i) matchC],sv')
	| SendAndTransition sat -> (ins@[mk_loc (loc i) ( checkSendAndTransition bps ss sat sv)]),sv
	| Fail -> (ins@[i]),sv

and

checkInstructions (bps:rFbIOPaths) (ss:stateSig IdMap.t) (sv:stateVars) (is:instructionL list) : (instructionL list * stateVars) =
	List.fold_left (checkInstruction bps ss) ([],sv) is

let containsSaTorF (is: instructionL list) : bool =
	List.exists (fun i-> match (unloc i) with Fail->true | SendAndTransition sat->true | _->false) is

let rec checkEndsAreSaTorF (is: instructionL list) : unit =
	match is with
	| [] -> raise (Failure "the instruction list cannot be empty")
	| {pl_loc=l;pl_desc=(SendAndTransition sat)} ::[] -> ()
	| {pl_loc=l;pl_desc=(SendAndTransition sat)}::ins::tl -> parse_error l (Some("The instructions after send and transition will not be executed"))
	| {pl_loc=l;pl_desc=Fail}::[] -> ()
	| {pl_loc=l;pl_desc=Fail}::ins::tl -> parse_error l (Some("The instructions after fail will not be executed"))
	| {pl_loc=l;pl_desc=(ITE (ex,tins,Some eins))}::[] -> checkEndsAreSaTorF tins; checkEndsAreSaTorF eins
	| {pl_loc=l;pl_desc=(ITE (ex,tins,Some eins))}::ins::tl when (containsSaTorF tins)&&(containsSaTorF eins) -> parse_error (loc ins) (Some("The instructions after if-then-else will not be executed since both branches contain send and transition or fail commands."))
	| {pl_loc=l;pl_desc=(Decode (id,ty,mIs,okins,erins))}::[] -> checkEndsAreSaTorF okins; checkEndsAreSaTorF erins
	| {pl_loc=l;pl_desc=(Decode (id,ty,mIs,okins,erins))}::ins::tl when (containsSaTorF okins)&&(containsSaTorF erins) -> parse_error (loc ins) (Some("The instructions after decode will not be executed since both branches contain send and transition or fail commands."))
	| ins::[] ->  parse_error (loc ins) (Some("Every branch of execution must end with send and transition or fail command."))
	| ins::tl -> checkEndsAreSaTorF tl

let checkMsgCode (bps:rFbIOPaths) (ss:stateSig IdMap.t) (sv:stateVars) (is:instructionL list) : instructionL list =
	let isC = fst (checkInstructions bps ss sv is) in
	checkEndsAreSaTorF isC;
	isC

let checkMessagePath (bps:rFbIOPaths) (mmc:msgMatchCode) : msgMatchCode =
	let path' = checkMsgPath (getIncomingMsgPaths bps) mmc.patternMatch.path in
	{patternMatch={portVar=mmc.patternMatch.portVar; path=path'; tupleMatch=mmc.patternMatch.tupleMatch}; code=mmc.code}

let checkMMcode (bps:rFbIOPaths) (ss:stateSig IdMap.t) (sv:stateVars) (mmc:msgMatchCode) : msgMatchCode =
	let mmc' = checkMessagePath bps mmc in 
	let sv' = checkMatchBindings bps mmc'.patternMatch sv in
	let code' = checkMsgCode bps ss sv' mmc'.code in
	{patternMatch=mmc'.patternMatch; code=code'}

let checkStateCode (bps:rFbIOPaths) (ss:stateSig IdMap.t) (sv:stateVars) (mmcodes:msgMatchCode list) : msgMatchCode list =
	let mmcodes' = List.map (fun mmc -> checkMMcode bps ss sv mmc) mmcodes in
	checkMsgMatchDeltas bps (List.map (fun mmc->mmc.patternMatch) mmcodes');
	mmcodes'

let getKeys (m:'a IdMap.t) : QidSet.t = 
		let lp=fst(List.split (IdMap.bindings m)) in
		List.fold_left (fun s p -> QidSet.add [p] s)QidSet.empty lp

let getInternalPorts (rF:funBody) : QidSet.t =
	QidSet.union (getKeys rF.parties) (QidSet.union (getKeys rF.params) (getKeys rF.subFuns))

let filterbIOPaths (bps:bIOPath list) (pfxs:string list located list) : bIOPath list =
	List.filter (fun bp -> List.exists (fun pfx -> (unloc pfx) = (fst bp) ) pfxs) bps

let getFbIOPaths (dirIOs:ioC IdMap.t) (advIOs:ioC IdMap.t) (f:funC) : rFbIOPaths =
	let uf = unloc f in
	let iddir = uf.idDirIO in
	let direct = getbIOPaths iddir iddir dirIOs in
	let adversarial = 
		match uf.idAdvIO with
		| Some id -> getbIOPaths id id advIOs
		| None -> []
	in
	{direct=direct; adversarial=adversarial; internal=[]}

let getRFbIOPaths (dirIOs:ioC IdMap.t) (advIOs:ioC IdMap.t) (funs:funC IdMap.t) (rF:funC) (p:partyDefC) : rFbIOPaths =
	let all = getFbIOPaths dirIOs advIOs rF in
	let urF = unloc rF in
	let filt = (unloc p).serves in
	let direct =  filterbIOPaths all.direct filt in
	let adversarial = filterbIOPaths all.adversarial filt in
	let internalSFM = IdMap.mapi (fun sfid (sf:subFunDeclC) -> 
let did = getDirIOIdImplByFun ((unloc sf).funId) funs in
getbIOPaths sfid did dirIOs ) urF.subFuns in
	let internalPM = IdMap.mapi (fun pid p -> 
		let did = unloc (unloc (fst p)) in
getbIOPaths pid did dirIOs ) urF.params in
	let internalM = IdMap.union (fun id p1 p2 ->raise (Failure "Impossible, we already checked params and subfuns have different ids")) internalSFM internalPM in
	let internal = IdMap.fold (fun id bps l -> l@bps) internalM [] in
	{direct=direct; adversarial=adversarial; internal=internal}

let checkState (urF:funBody) (states:stateC IdMap.t) (bps:rFbIOPaths) (s:stateC) : stateC =
	let us = unloc s in
	let sv = initStateVars (unloc s) (getInternalPorts urF) [] in
	let ss = getStateSigs states in
	let mmcodes'= checkStateCode bps ss sv us.mmcodes in
	mk_loc (loc s) {isInitial=us.isInitial; params=us.params; vars=us.vars; mmcodes=mmcodes'}

let checkPartyCode dirIOs advIOs funs =
	IdMap.map 
		(fun rF ->
		let urF = unloc rF in 
		let parties = urF.parties in
		let parties'= IdMap.map 
			(fun p ->
			let up = unloc p in
			let bps = getRFbIOPaths dirIOs advIOs funs rF p in
			let states = up.code in
			let states'= IdMap.map (checkState urF states bps) states
			in
			mk_loc (loc p) {serves=up.serves; code = states'}
			) parties
		in
		let states = urF.states in
		let bps = getFbIOPaths dirIOs advIOs rF in
		let states'= IdMap.map (checkState urF states bps) states
		in
		mk_loc (loc rF) {params=urF.params; idDirIO=urF.idDirIO; idAdvIO=urF.idAdvIO; subFuns=urF.subFuns; parties=parties'; states=states'}
		) funs

let getSFRefsToFInRF (funs:funC IdMap.t) (fid:string) : IdSet.t =
	let rfb = IdMap.find fid funs in
	let sfrf = IdMap.filter (fun key r -> existsId funs (unloc r).funId) (unloc rfb).subFuns in
	IdMap.fold (fun key r set -> IdSet.add (unloc r).funId set) sfrf IdSet.empty

let checkCircRefsInRFuns (rfs:funC IdMap.t) = checkCircRefs getSFRefsToFInRF rfs

let checkFuns (funMap: funDef IdMap.t) (dirIOs: ioC IdMap.t) (advIOs: ioC IdMap.t) : funC IdMap.t =
	let eFId = existsId funMap in 
	let funs = IdMap.map (checkFunDecl eFId dirIOs advIOs) funMap in
	checkCircRefsInRFuns funs;
	checkSubFunParams funs;
	checkPartyCode dirIOs advIOs funs
	

(*-------------------------*)


(*Simulator checks*)

let checkMsgCodeSim (fbps: rFbIOPaths) (ss: stateSig IdMap.t) (mmc:msgMatchCode) (sv: stateVars) : msgMatchCode =
	let code'= checkMsgCode fbps ss sv mmc.code in
	{patternMatch=mmc.patternMatch; code=code'}

let checkMessagePathSim (bps: bIOPath list) (isini:bool) (mmc:msgMatchCode) : unit =
	let bps = filterbIOPs In bps in
	let mp = mmc.patternMatch.path in
	let l = msgLoc mp in
	let id =fst (List.find (fun p-> (List.length (fst p))=1) bps) in
	if isini && ((unlocs mp.ioPath)<>id) then parse_error l (Some("Initial state can handle only messages comming from ideal functionality. Did you omit prefix "^(List.hd id)^".?"))
	else	
	(
	let iops = fst(List.split bps) in
	let invalidDest() = parse_error l (Some("Not a valid destination, these destinations are valid:"^(string_of_IOpaths iops) )) in
	let umpiop = (unlocs mp.ioPath) in
	match mp.msgType with
	| MsgType mt ->	if not(List.mem umpiop iops) then invalidDest() else
			if List.exists (fun bp -> (fst bp)=umpiop && IdMap.mem (unloc mt) (snd bp)) bps then ()
			else parse_error (loc mt) (Some((unloc mt)^" is not an incoming message of "^(string_of_IOpath umpiop)))
	| OtherMsg _ -> if (List.exists (fun p-> sl1_starts_with_sl2 p umpiop) iops) then () else invalidDest()
	)

let checkMatchBindingsSim (bps: bIOPath list) (sv: stateVars) (mmc:msgMatchCode) : stateVars =
	let mm = mmc.patternMatch in
	checkTupleMatch bps mm sv

let checkMsgMatchDeltasSim (rfbps:rFbIOPaths) (mmcodes:msgMatchCode list) : unit =
	let mps = getIncomingMsgPaths rfbps in
	ignore (checkMMDsNonEmpty mps (List.map (fun mmc->{ioPath=mmc.patternMatch.path.ioPath; msgType=mmc.patternMatch.path.msgType}) mmcodes))

let checkSimStateCode (bps: bIOPath list) (ss: stateSig IdMap.t) (sv: stateVars) (isini:bool) (mmcodes:msgMatchCode list) : msgMatchCode list =
	List.iter (checkMessagePathSim bps isini) mmcodes;
	let svs = List.map (checkMatchBindingsSim bps sv) mmcodes in
	let fbps = {direct=[]; adversarial=bps; internal=[]} in
	let ret = List.map2 (checkMsgCodeSim fbps ss) mmcodes svs in
	checkMsgMatchDeltasSim fbps ret;
	ret

let disj (k:'key) (a1:'a) (a2:'a) =
	raise (Failure "Not disjoint!")

let disjUnion (qml: 'a QidMap.t list): 'a QidMap.t =
	List.fold_left (fun qm1 qm2 -> QidMap.union disj qm1 qm2) QidMap.empty qml

let getSimComponents (funs: funC IdMap.t) (rF:string) (ps:string list) : funBody QidMap.t =
	let rec getSC (funs: funC IdMap.t) (fid:string) (pfx:SL.t) : funBody QidMap.t =
		if IdMap.mem fid funs
		then	
			let urf = unloc(IdMap.find fid funs) in
			disjUnion
			(	
			(QidMap.singleton pfx (urf))
			::
			(IdMap.fold (fun sfid sfd l-> (getSC funs (unloc sfd).funId (pfx@[sfid]))::l ) urf.subFuns [])
			)
		else raise (Failure "Impossible! We already checked that all referenced functionalities exist")
	in
	let urf = unloc(IdMap.find rF funs) in
	let pids = IdMap.fold (fun pid x l -> pid::l) urf.params [] in
	let qpids = List.map (fun pid -> rF::[pid]) pids in
	disjUnion
	(
	(getSC funs rF [rF])
	::
	(List.map2 (getSC funs) ps qpids)
	)
		
let getComponentIOPaths (advIOs: ioC IdMap.t) (f:funBody) : bIOPath list =
	match f.idAdvIO with
		| Some id -> getbIOPaths id id advIOs 
		| None -> []


let invertDir (dir:msgInOut) = 
	match dir with In->Out | Out->In
let invertMDF (mdf:messageDefBody) : messageDefBody = 
	{direction=(invertDir mdf.direction); content=mdf.content; portLabel=mdf.portLabel}
let invertMDFl (mdfl:messageDefBody located) : messageDefBody located =
	let l = loc mdfl in
	let mdf = unloc mdfl in
	let mdf'= invertMDF mdf in
	mk_loc l mdf'
let invertbIObC (bio:basicIObodyC):basicIObodyC =
	IdMap.map invertMDFl bio
let invertMsgDirs (bp:bIOPath) : bIOPath =
	let bio = snd bp in
	let bio'= invertbIObC bio in
	((fst bp),(bio'))

let getSimbIOPaths (advIOs: ioC IdMap.t) (uses:string) (cs:funBody QidMap.t) : bIOPath list =
	let sbps = QidMap.map (getComponentIOPaths advIOs) cs in	
	let bps = QidMap.add [] (List.map (fun bp ->invertMsgDirs bp) (getbIOPaths uses uses advIOs)) sbps in
	QidMap.fold ( fun q bpl l -> l@(List.map ( fun bp-> ((q@(fst bp)),(snd bp)) ) bpl) ) bps []

let getSimInternalPorts (cs:funBody QidMap.t) : QidSet.t =
	let rcsips = QidMap.map (fun fb-> getInternalPorts fb ) cs in
	let rcsqips = QidMap.mapi (fun q ips -> QidSet.map (fun ip-> q@ip) ips) rcsips in
	QidMap.fold (fun q qips sip -> QidSet.union qips sip) rcsqips QidSet.empty
	
let checkSimCode (dirIOs: ioC IdMap.t) (advIOs: ioC IdMap.t) (funs: funC IdMap.t) (sim:simDefC) : simDefC = 
	let usim = unloc sim in
	let states = usim.body in
	let ss = getStateSigs states in
	let cs = getSimComponents funs usim.sims usim.simsParamIds in
	let bps = getSimbIOPaths advIOs usim.uses cs in
	let states'= IdMap.map 
		(fun s ->
		let us = unloc s in
		let sv = initStateVars us (getSimInternalPorts cs) ["simulator"] in
		let mmcodes'= checkSimStateCode bps ss sv us.isInitial us.mmcodes in
		mk_loc (loc s) {isInitial=us.isInitial; params=us.params; vars=us.vars; mmcodes=mmcodes'}
		) states
		in
	mk_loc (loc sim) {uses=usim.uses; sims=usim.sims; simsParamIds=usim.simsParamIds; body=states'}


let checkExistsF (funs: funC IdMap.t) (rf:id) =
	let urf = unloc rf in
	if existsId funs urf then ()
	else parse_error (loc rf) (Some("Functionality "^urf^" doesn't exist."))

let checkIsRealF (funs: funC IdMap.t) (rf:id) =
	checkExistsF funs rf;
	let f = unloc (IdMap.find (unloc rf) funs) in
	if f.parties = IdMap.empty then parse_error (loc rf) (Some("The simulated functionality must have parties."))

let checkSimFunParams (funs: funC IdMap.t) (i2sIOs: ioC IdMap.t) (rf:id) (params:id list) =
	let dIOs = getParamDirIOIds funs (unloc rf) in
	let dIOs'= List.map (fun id->getDirIOIdImplByFun id funs) (unlocs params) in
	if (List.length dIOs)<>(List.length dIOs')
	then parse_error (loc rf) (Some("Wrong number of parameters for functionality."))
	else List.iteri (fun i pid -> if (List.nth dIOs i)<>(List.nth dIOs' i) then parse_error (loc pid) (Some("Parameter implements different directIO than required by functionality."))) params;
	List.iter (fun pid -> let f= unloc (IdMap.find (unloc pid) funs) in
		if f.parties<>IdMap.empty then parse_error (loc pid) (Some("The parameter to simulated functionality cannot have parties")) else
		match f.idAdvIO with
		| None -> parse_error (loc pid) (Some("The parameter to simulated functionality must implement an adversarialIO"))
		| Some id -> () (*we already checked that it is not composite when checking FunDecl for partyless funs*)
	) params


let checkSimDecl (dirIOs: ioC IdMap.t) (i2sIOs: ioC IdMap.t) (funs: funC IdMap.t) (sd: simDef) : simDefC =
	checkExistsI2SIO i2sIOs sd.uses;
	let uses = unloc sd.uses in
	checkIsRealF funs sd.sims;
	let sims = unloc sd.sims in
	List.iter (checkExistsF funs) sd.simsParamIds;
	checkSimFunParams funs i2sIOs sd.sims sd.simsParamIds;
	let simsParamIds = unlocs sd.simsParamIds in
	let body = checkStates sd.id sd.body in
	mk_loc (loc sd.id) {uses=uses; sims=sims; simsParamIds=simsParamIds; body=body}

let checkSimulators (simMap: simDef IdMap.t) (dirIOs: ioC IdMap.t) (advIOs: ioC IdMap.t) (funs: funC IdMap.t) : simDefC IdMap.t =
	let sims = IdMap.map (checkSimDecl dirIOs advIOs funs) simMap in
	IdMap.map (checkSimCode dirIOs advIOs funs) sims
(*----------------*)

(*DL prog checks*)

let getIOId ioDef = match ioDef with
		| AdversarialIO io -> io.id
		| DirectIO io      -> io.id

let getDefId (def:def) = match def with
		| IODef iod -> getIOId iod
		| FunDef fd -> fd.id
		| SimDef sd -> sd.id

let filterMap (fm:'a-> 'b option) (m:'a IdMap.t) : 'b IdMap.t =
	let flt = IdMap.filter (fun id def -> match fm def with Some x -> true| None -> false) m in
	IdMap.map (fun def -> match fm def with Some x -> x | None -> raise (Failure "!impossible!")) flt

let checkDefs defL =
		let defMap = checkUniqueId defL getDefId in

		let dirIOMap = filterMap (fun def -> match def with IODef DirectIO io ->Some io | _->None) defMap in
		let advIOMap = filterMap (fun def -> match def with IODef AdversarialIO io ->Some io | _->None) defMap in
		let funMap = filterMap (fun def -> match def with FunDef f ->Some f | _->None) defMap in
		let simMap = filterMap (fun def -> match def with SimDef sd ->Some sd | _->None) defMap in

		let dirIOs = checkDirIOs dirIOMap in
		let advIOs = checkAdvIOs advIOMap in
		let funs = checkFuns funMap dirIOs advIOs in
		let sims = checkSimulators simMap dirIOs advIOs funs in
		{ directIOs = dirIOs;
		  adversarialIOs = advIOs;
		  functionalities = funs;
		  simulators = sims }

let loadUcImports imps : def list =[]

let loadEcReqs reqs =
		let reqimp idl =
			try UcEcInterface.requireImport (unloc idl)
			with Failure f -> parse_error (loc idl) (Some("Error when require import-ing "^(unloc idl)^" :"^f))
		in
		List.iter reqimp reqs

let checkDL dlprog =
		UcEcInterface.init();
		loadEcReqs dlprog.externals.ecRequirements;
		let extDefs = loadUcImports dlprog.externals.dlImports in
		checkDefs (extDefs @ dlprog.definitions);

(*--------------*)

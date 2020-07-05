(* ucExpressions.ml *)

open UcParseTree
open UcTypechecked
open UcTypes
open EcLocation
open UcUtils

let builtinOperators = IdMap.add "envport" (boolType,[portType]) IdMap.empty

let getOpSig (id:id) : typ*typ list =
	let op = unloc id in
	if (IdMap.mem op builtinOperators) then IdMap.find op builtinOperators else
	if (UcEcInterface.existsOperator op) = false then parse_error (loc id) (Some "Nonexisting operator or function.")
	else UcEcInterface.getOperatorSig op

let checkNullaryOp (id:id) : typ =
	let opsig = getOpSig id in
	if (snd opsig)<>[] then parse_error (loc id) (Some ("Nullary operator expected, operator "^(unloc id)^" has arguments." ))
	else fst opsig

let checkExprId (sv:qid->typ) (qid:qid) : typ =
	try sv qid	
	with Not_found -> 
		try (
			match qid with
			| id::[] -> checkNullaryOp id 
			| _ -> raise Not_found
		    )		
		with Not_found ->
			parse_error (mergelocs qid) (Some ("Nonexisting variable or constant: "^(string_of_IOpath(unlocs qid))))



let rec checkExpression (sv:qid->typ) (expr:expressionL) : typ =
	match (unloc expr) with
	| Id id -> checkExprId sv id
	| Tuple el -> if ((List.length el)=1)
			then (checkExpression sv (List.hd el))
			else Ttuple (List.map (fun e -> checkExpression sv e) el) 
	| App (fid,el) -> checkSig sv fid el
	| Enc e -> ignore (checkExpression sv e); univType

and checkSig sv fid el = 
	let op = unloc fid in
	let opsig = getOpSig fid in
	let tl = snd opsig in
	let farno = List.length tl in
	let arno = List.length el in
	if farno<>arno then parse_error (loc fid) (Some (op^" expects "^(string_of_int farno)^" arguments, "^(string_of_int arno)^" arguments provided"))
	else
	checkSigTypes fid sv tl el;
	fst opsig

and checkSigTypes (_:id) (sv:qid->typ) (tl:typ list) (el:expressionL list) : unit =
	let tel=List.combine tl el in
	let teli = fst (List.fold_left (fun (l,i) (t,e) ->(((t,e),i)::l,i+1) ) ([],1) tel) in
	let telic = List.filter (fun ((t,_),_) -> match t with Tconstr _ ->true | _->false) teli in
	List.iter 
(fun ((t,e),i) -> let et=(checkExpression sv e) in if t<>et then parse_error (loc e) (Some ("Type mismatch for "^(string_of_int i)^". argument. Expected type:" ^ (string_of_typ t) ^". Provided type:"^ (string_of_typ et) ^".")) else ())
	  telic;
	let teliv = List.filter (fun ((t,_),_) -> match t with Tvar _ ->true | _->false) teli in
	List.iter (fun ((t,_),i) ->
			let telivt = List.filter (fun ((t',_),_)-> t'=t ) teliv in
			let e = snd(fst(List.hd telivt)) in
			let te = checkExpression sv e in
			List.iter (fun ((_,e'),i') ->
					if te<>(checkExpression sv e')
					then parse_error (loc e') (Some ("Type mismatch, "^(string_of_int i)^". and "^(string_of_int i')^". argument must have the same type."))
					else ()
				) telivt
		  ) teliv

let isDistribution (etyp:typ) : bool =
	match etyp with
	| Tconstr ("distr",_) -> true
	| _ -> false

let getDistrubutionTyp (etyp:typ) : typ =
	match etyp with
	| Tconstr ("distr",dtyp) ->	begin
			match dtyp with 
			| Some t -> t 
			| None -> raise (Failure "Distribution of type None was not expected.")
				end
	| _ -> raise (Failure "Distribution was expected.")

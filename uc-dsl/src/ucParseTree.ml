open EcLocation

exception ParseError of EcLocation.t * string option
let parse_error loc msg = raise (ParseError (loc, msg))

exception ParseError2 of EcLocation.t * EcLocation.t * string
let parse_error2 loc1 loc2 msg = raise (ParseError2 (loc1, loc2, msg))

type stringL = string located
type id = stringL

type msgInOut =
	| In
	| Out

type ty =
	| NamedTy of id
	| TupleTy of ty list

type nameType = {id:id; ty:ty}

type messageDef = {direction:msgInOut; id:id; content:nameType list; portLabel: id option}


type basicIObody = messageDef list

type ioItem = {id:id; ioId:id}

type compositeIObody = ioItem list

type ioBody =
	| Basic of basicIObody
	| Composite of compositeIObody

type io = {id:id; body:ioBody}

type ioDef =
	| DirectIO of io
	| AdversarialIO of io

type funParam = {id:id; idDirIO:id}

type subFunDecl = {id:id; funId:id; funParamIds: id list }

type msgType =
	| MsgType of id
	| OtherMsg of EcLocation.t

type qid = id list

type msgPath = {ioPath: qid; msgType:msgType}

type matchItem =
	| Const of id
	| ConstType of nameType
	(*| Tuple of matchItem list located*)
	| Wildcard of EcLocation.t

type msgMatch = {portVar:id option; path:msgPath; tupleMatch:matchItem list option}

type expression =
	| Id    of qid
	| Tuple of expressionL list
	| App   of id * expressionL list
	| Enc	of expressionL

and expressionL = expression located

type msgInstance = {path:msgPath; tupleInstance:expressionL list; portVar:id option}

type stateInstance = {id:id; params:expressionL list option}

type sendAndTransition = {msg:msgInstance; state:stateInstance}

type instruction =
	| Assign of id*expressionL
	| Sample of id*expressionL
	| ITE of expressionL*(instructionL list)*(instructionL list option)
	| Decode of expressionL*ty*matchItem list*instructionL list* instructionL list
	| SendAndTransition of sendAndTransition
	| Fail
and instructionL = instruction located

type msgMatchCode = {patternMatch:msgMatch; code: instructionL list;}

type stateCode = {vars:nameType list; mmcodes:msgMatchCode list}

type state = {id:id; params:nameType list ; code:stateCode}
		
type stateDef =
	| InitialState of state
	| FollowingState of state 

type partyDef = {id:id; serves:qid list; code:stateDef list}

type subItem =
	| SubFunDecl of subFunDecl
	| PartyDef of partyDef

(*either stateBody is empty or both params and body are empty*)
type funDef = {id:id; params:funParam list; idDirIO:id; idAdvIO:id option; body:subItem list; stateBody:stateDef list}

type simDef = {id:id; uses:id; sims:id; simsParamIds: id list; body:stateDef list }

type def =
	| IODef  of ioDef
	| FunDef of funDef
	| SimDef of simDef


type externals = {ecRequirements:id list; dlImports:id list}

type dlprog = {externals:externals; definitions:def list}

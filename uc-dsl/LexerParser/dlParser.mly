

%{

open EcUtils
open EcLocation
open DlParseTree

let toId (mtid:msgType) =
	match mtid with
	| MsgType id -> id
	| OtherMsg l -> parse_error l (Some "othermsg keyword cannot be followed by '.' ")

let rec r_mtl2msgPath (mtl:msgType list) (mp:msgPath)=
	match mtl with
	| [] -> raise (Failure "Cannot happen: empty list when converting mtl to msgPath")
	| [x] -> {ioPath = mp.ioPath;msgType = x}
	| hd::tl -> r_mtl2msgPath tl {ioPath = mp.ioPath @ [toId hd]; msgType = mp.msgType}

let mtl2msgPath (mtl:msgType list) = r_mtl2msgPath mtl {ioPath=[];msgType=OtherMsg _dummy}


%}


%token <string> ID
%token LPAREN
%token RPAREN
%token LBRACE
%token RBRACE
%token COMMA
%token COLON
%token DIRIO
%token ADVIO
%token IN
%token OUT
%token MESSAGE
%token EOF
%token FUNCT
%token SIM
%token SIMS
%token IMPLEM
%token EQ
%token PARTY
%token SERVES
%token USES
%token DOT
%token INITIAL
%token STATE
%token MATCH
%token WITH
%token END
%token PIPE
%token AT
%token OTHERMSG
%token ARROW
%token FAIL
%token SEND
%token ANDTXT
%token TRANSITION
%token REQUIRES
%token IMPORT
%token SUBFUN
%token UNDERSCORE

%token VAR
%token ASGVAL
%token ASGSAMPLE
%token SEMICOLON
%token IF
%token ELIF
%token ELSE

%token ENCODE
%token DECODE
%token AS
%token OK
%token ERROR


%token AND
%token OR
%token HAT
%token NOT
%token STAR
%token <string>  ROP4
(*
Operators and their associativity are copied from ecParser.mly of easycrypt project.
dlLexer.mll contains code from ecLexer.mll for recognizing operators.
The operators and code are a small subset of what can be found in easycrypt.
*)

%right    OR
%right    AND
%nonassoc NOT
%nonassoc EQ 
%left   HAT
%right ROP4

%nonassoc ENCODE

(*
The input for the dlParser is a list of tokens produced by dlLexer from the uc dsl file.
This list is parsed by the dlParser, starting with the initial production prog.
The output of dlParser is a record of dlprog type (defined in dlParseTree.ml).
This record is an input to the checkDl function (defined in dl.ml) which checks the uc dsl file for correctness,
If there are errors checkDl raises a ParseError (or ParseError2) exception (defined in dlParseTree.ml),
These contain the location (or two) of error together with some error message.
The location type is defined in ecLocation.ml - from the EasyCrypt project.
If there are no errors checkDl will return a record of type dlprogC (defined in dlParsedTree.ml)
The dlprogC is intended to be the input to the code generator which outputs easycrypt code.
checkDl is called by dlParseFile.ml, which in turn is called by: 
checkDl.ml, with a filename as command line argument, outputs parse error (if any) to command line;
tests.ml runs a list of tests defined in testSuite.ml and outputs the test results to command line;
makeTestCase.ml, with a filename as command line argument, outputs the result of checkDl as ocaml code representing the test case.
*)
%start <DlParseTree.dlprog> prog

%%

%inline loc(X):
| x=X {
    { pl_desc = x;
      pl_loc  = EcLocation.make $startpos $endpos;
    }
  }

%inline idL:
| idL=loc(ID) { idL }

%inline qid:
| qid=separated_nonempty_list(DOT,idL) { qid }

(*
uc dsl file consists of a preamble which references other .ec and .uc files,
and a list of definitions of direct and adversarial interfaces, functionalities and simlators.
*)
prog:
	| ext = preamble; defs = list(def); EOF { {externals=ext; definitions=defs} }
	;
	
preamble:
	| reqs = option(reqs); imps = option(imps);  { {ecRequirements= (match reqs with | None -> [] | Some r-> r); dlImports = (match imps with | None ->[] | Some i->i )} }

(*Importing is supposed to load content from other .uc files - not yet implemented*)
imps :
	| IMPORT imps=nonempty_list(idL) DOT { imps }

(*
Requires references easycrypt files, these are loaded by loadEcReqs (dl.ml)
which calls requireImport (dlEcInterface.ml) which executes an "import require" easycrypt command.
This loads the content of the .ec theory in the easycrypt environment which is later queried for types and operators
*)
reqs:
	| REQUIRES reqs=nonempty_list(idL) DOT { reqs }

(*
A definition is either a definition of an interface, a functionality or a simulator.
All of the names must be distinct (checked by checkDefs in dl.ml, tested by testDuplicateIdInIODefinitions, testRealFunIdSameAsIOid,)
*)
def:
	| iod  = ioDef;  {IODef iod  }
	| fund = funDef; {FunDef fund}
	| simd = simDef; {SimDef simd}
	;

(*Interfaces*)

(*
An interface can either be direct or adversarial.
Both need to satisfy the same rules, so they are checked by the same function, checkADIOs (dl.ml)
checkADIOs returns an IdMap of type ioC (defined in dlParsedTree.ml). 
The keys of the are the names of the interfaces, and ioC contains the same information as io in dlParseTree.ml,
except for the message parameters - these contain additional type information.
*)

ioDef:
	| iod = dirio;       { iod }
	| iod = advio;       { iod }

dirio:
	| DIRIO; io = dio;	{DirectIO io}

dio:
	| name = idL; LBRACE; iob = dioBody; RBRACE;{ {id=name; body=iob}:io }

advio:
	| ADVIO; io = aio;    	{AdversarialIO io}

aio:
	| name = idL; LBRACE; iob = aioBody; RBRACE;{ {id=name; body=iob}:io }

(*A direct interface is either basic or composite, same as adversarial interface*)
dioBody:
	| iob = dbasicIObody;  {Basic iob    }
	| iob = nonempty_list(ioItem); {Composite iob}

aioBody:
	| iob = abasicIObody;  {Basic iob    }
	| iob = nonempty_list(ioItem); {Composite iob}

(*
A composite interface consists of list of name:ioType pairs
The names must be unique (checked by checkCompIoBody, tested by testDuplicateIdInCompositIOBody)
The ioType must be the name of an existing basic direct interface. 
(checked by: checkExistsIO, checkCompositesRefBasics; tested by: 
testNonExistingDirIoIdInCompositeBody, 
testCompositeDirIOreferencingNonDirIO, 
testNonExistingAdvIoIdInCompositeBody, 
testCompositeAdvIOreferencingNonAdvIO, 
testCompositeReferencingComposite, 
testCircularReferenceSelfReference)
*)
ioItem:
	| name = idL; COLON; ioType = idL; { {id=name; ioId=ioType} }

(*
A basic interface has a list of message definitions.
A Message definition has a direction, a name, and a list of parameters.
The message names within an interface must be unique 
(checked by: checkBasicIoBody; tested by: testDuplicateMessageId)
Additionally, incomming direct messages have a source identifier, and outgoing messages have a destination identifier.
These identifiers can be anything and are not subject to any checks, their purpose is to document the intended sender/recipient of the message.
*)
dbasicIObody: 
	| iob = nonempty_list(dmessageDef); { iob }

abasicIObody: 
	| iob = nonempty_list(amessageDef); { iob }


dmessageDef:
	| IN;  pl=idL; AT; name = idL; LPAREN; cont = params; RPAREN; { {direction = In;  id = name; content=cont; portLabel=Some pl} }
	| OUT; name = idL; LPAREN; cont = params; RPAREN; AT; pl=idL; { {direction = Out; id = name; content=cont; portLabel=Some pl} }

msgInOut:
	| IN  { In  }
	| OUT { Out }

amessageDef:
	| dir = msgInOut; name = idL; LPAREN; cont = params; RPAREN; { {direction = dir; id = name; content=cont; portLabel=None} }

params:
	| ps = separated_list(COMMA,nameType) { ps }

(*
The content of the message is a list of parameters, these are name:type pairs.
The names must be unique, however, the names of the parameters are not used, their purpose is to document the intended meaning of the parameter.
When the message is later sent or received, only the position (index) of the parameters is relevant, and not the name.
To check the type, the checkParams function calls checkType (dlEcTypes.ml) which first tries to find the type among built-in types (dlTypes.ml),
and if not found it tries to find the type in easycrypt environment by calling existsType from dlEcInterface.ml.
The checkType will either raise exception if the type is not found, or return a typ (defined in dlTypes.ml).
(checked by: checkParams; tested by: 
testDuplicateParameterId,
testDirectIOTupleNonexistingType)

The typ type is a simplified version of ty type from ecTypes.ml, for more info on what was removed from ecTypes look at documentation in dlTypes.ml.
The checkParam function returns an IdMap of typC (dlParsedTree.ml), with keys being names from name:type pairs, 
and typC contains both the typ of the parameter and the index of the parameter in the list of the name:type pairs.
*)

nameType:
	| name = idL; COLON; t = ty; { {id=name; ty=t} }

ty:
	| name = idL;                                               	{ NamedTy name           }
	| tuphd=tyBr; STAR; tuptl=separated_nonempty_list(STAR,tyBr);	{ TupleTy (tuphd::tuptl) }

tyBr:
	| name = idL;                                               			{ NamedTy name           }
	| LPAREN; tuphd=tyBr; STAR; tuptl=separated_nonempty_list(STAR,tyBr); RPAREN;	{ TupleTy (tuphd::tuptl) }
(*----------*)

(*Functionalities*)
(*
Functionalities are checked by checkFuns function (dl.ml)
There are two different types of functionalities - real and ideal.
For both of them the implemented interfaces must exist, and the direct interface must be composite.
An ideal functionality must implement a basic adversarial interface, while a real functionality can optionally implement a composite adversarial interface.
(checked by: checkFunDecl; tested by: 
testRealFunImplements2DirIOs, 
testRealFunImplements2AdvIOs, 
testIdealFunImplements2DirIOs, 
testIdealFunImplements2AdvIOs,
testIdealFunImplementsCompositeAdvIO)

A real functionality can have parameters which is a list of name:interface pairs.
The parameter names are unique and interfaces are direct and composite (and thus can be implemented by a functionality).
(checked by: checkRealFunParams tested by:
testRealFunParamIONonExisting,
testRealFunParamIdNotUnique,
testRealFunParamIONotComposite,
testRealFunParamIOAdversarial
)
*)
funDef:	
	| FUNCT; name=idL; parameters = funParams; IMPLEM; dirIo=idL; advIo=option(idL); rfBody = realFunBody; { {id=name; params=parameters; idDirIO=dirIo; idAdvIO=advIo; body=rfBody; stateBody=[]} }

	| FUNCT; name=idL; LPAREN; RPAREN; IMPLEM; dirIo=idL; advIo=option(idL); rfBody = realFunBody; { {id=name; params=[]; idDirIO=dirIo; idAdvIO=advIo; body=rfBody; stateBody=[]} }

	| FUNCT; name=idL; LPAREN; RPAREN; IMPLEM; dirIo=idL; advIo=option(idL); ifBody = partyCode; { {id=name; params=[]; idDirIO=dirIo; idAdvIO=advIo; body=[]; stateBody=ifBody} }
	;

funParams:
	| LPAREN; fps = separated_nonempty_list(COMMA,funParam); RPAREN; { fps }
	;

funParam: 
	| name=idL; COLON; idDirIO=idL { {id=name; idDirIO=idDirIO}:funParam }
	;

realFunBody:
	| LBRACE; sil = nonempty_list(subItem); RBRACE;{ sil }
	;
(*
The body of a real functionality consists of subfunctionalities and parties. Their names must be unique and different from the names of the parameters.
The subfunctionality must have a type of an existing functionality, and it's parameters must be other subfunctionalities and parameters.
(checked by checkSubFunDecl, checkFunDecl; tested by:
testSubFunNonExistingFun,
testDuplicateSubFunId,
testSubFunIdSameAsParamId
)

Once the declarations of all functionalities are checked, the subfunctionalities are further checked by
for circular references (a functionality cannot be its own subfunctionality),
(checked by checkCircRefsInRFuns; tested by:
testCircFunRefSingleStep,
testCircFunRefTwoSteps
)

and the prameters are checked to match the direct interface types of subfunctionality.
(checked by checkSubFunParams; tested by:
testSubFunRFWrongParamNo,
testSubFunRFWrongParamTypeIF,
testSubFunRFWrongParamTypeRF,
testSubFunRFWrongParamTypeParam,
testSubFunIdSameAsParamId)
*)
subItem:
	| sfd = subFunDecl { SubFunDecl sfd }
	| pd  = partyDef   { PartyDef   pd  }
	;

subFunDecl:
	| SUBFUN; name = idL; EQ; funName = idL; params=paramList;  { {id=name; funId=funName; funParamIds=params}:subFunDecl }
	;

paramList:
	| LPAREN; params=separated_list(COMMA,idL); RPAREN; { params }

(*
The party serves exactly one basic direct interface that is a component of the composite direct interface implemented by the functionality;
the party serves at most one basic adversarial direct interface hat is a component of the composite adversarial interface implemented by the functionality.
(checked by: checkPartyDecl; tested by:
testPartyServesDeclNoDirIO,
testPartyServesDeclTwoDirIO,
testPartyServesDeclIOItemNotASubIO,
testPartyServesDeclNotInDirIO,
testPartyServesDeclMultipleInIOs)

The parties can't serve the same basic interfaces, and the union of the basic interfaces served by the parties sums up to composite interfaces implemented by the functionality.
(checked by: checkPartiesServeDirectSum; tested by:
testPartiesServeSameIO,
testPartiesDontServeEntireDirIO,
testPartiesDontServeEntireAdvIO)
*)
partyDef:
	| PARTY; name=idL; serves=serves; code=partyCode { {id=name;serves=serves;code=code} }
	;

serves:
	| SERVES; sl=separated_list(COMMA,qid) { sl }


partyCode:
	| LBRACE; sdl=nonempty_list(stateDef) RBRACE;{ sdl }
	;

(*

The party code consists of a list of states.
The states must have unique names, and there must be exactly one initial state.
(checked by: checkStates; tested by:
testPartyNoInitialState,
testPartyMultipleInitialStates,
testPartyDuplicateStateId
)

Individual state's parameters and variables must have unique names and their types must exist.
(checked by: checkStateDecl, checkParams; tested by:
testStateParamsDuplicateIds,
testStateParamsNonExistingType,
testStateParamNonExistingType,
testStateVarsDuplicateIds,
testStateVarParamDuplicateIds,
testStateVarsNonExistingType,
testStateVarNonExistingType)

*)
stateDef:
	| INITIAL; STATE; name=idL; code=stateCode; 
		{ InitialState   {id=name; params=[]; code=code}     }
	| STATE; name=idL; LPAREN; params=params; RPAREN; code=stateCode;          
		{ FollowingState {id=name; params=params; code=code} }

stateCode: 
	| LBRACE; vars = localVarDecls; codes = messageMatchCodes; RBRACE; { {vars=vars; mmcodes=codes} }
	;

localVarDecls:
	| lvds = list(localVarDecl) { List.flatten lvds }

localVarDecl:
	| VAR; lvs = nonempty_list (idL); COLON; t=ty SEMICOLON; { List.map (fun lv -> {id=lv; ty=t}) lvs }

(*
Incomming messages are matched against a list of possible messages contained in a rFbIOPaths record.
This record contains three fields: direct, adversarial and internal, each field is a list of bIOPaths,
and a bIOPath is a pair of a string list (a path) and a basic interface.
For a party (or an ideal functionality) the rFbIOPaths record is constructed in checkPartyCode function,
by making calls to getRFbIOPaths (or getFbIOPaths) function.

The rFbIOPaths for a party will contain a single path for the basic direct interface the party is serving, 
a single path for the basic adversarial interface the party is serving (or empty list if the party doesn't serve adversarial interface)
and every component of the direct interface implemented by a subfunctionality or functionalities parameter will have a bIOPath in the internal field of the rFbIOPaths record.

The internal field of a rFbIOPath record for an ideal functionality will be an empty list, 
the adversarial field will contain a single path to the adversarial interface of the functionality,
and the direct field will contain a path for each of the components of the composite interface implemented by the functionality.

The code of the state consists of a single match message statement containing a list of possible message matches together with the list of statements handling the matched message.

The match consists of a message path followed by the message type and an optional binding of message parameters to local constants.
The message path is a sequence of strings, starting with the component (subfunctionality or parameter) name (or empty string if the component is the functionality itself), followed by the name of the implemented interface, followed by the component of the interface.
The message type can be a message from the basic interface or "othermsg" keyword covering all the messages contained in the path.
The message path doesn't have to be complete when "othermsg" is used, e.g. componentName.othermsg will match against all of the messages comming from that component of the functionality and just othermsg will match against all messages.

The checkState function initializes the stateVars record - it contains the information about current scope. 
Initially it contains the state parameters as constants, state variables as uninitialized variables, and names of parties, subfunctionalities and parameters as internal ports. These can be used in code as constants of type port.
Furthermore, the signatures of all of the states of the party are collected,
a signature is a typ list containing the types of the state parameters.
These signatures are used to check transitioning to a state.

The checkStateCode function calls checkMMcode on every message match,
and the entire match message statement is checked to ensure all of the messages are matched,
and that every match is not covered by a previous match. 
(checked by checkMsgMatchDeltas; tested by:
testMsgMatchAlreadyCovered,
testMsgMatchIncomplete,
testIdealFunMsgMatchIncomplete)

The checkMessagePath function filters the rFbIOPaths record so that the basic interfaces contain only messages the party can receive;
these are the incomming messages of the direct and adversarial fields, 
and the outgoing messages from the internal field of the rfbIOPaths.
The paths of the messages do not need to be fully qualified if there is no ambiguity- 
they can contain only message type instead of the full path (e.g. just messageTypeName instead of compositeIOname.componentName.messageTypeName)
or just the basic interface name followed by the message type (e.g. componentName.messageTypeName instead of compositeIOname.componentName.messageTypeName).
When matching internal messages, the fully qualified path must be used.
(checked by: checkMsgPath; tested by:
testMsgMatchUnexpected,
testMsgMatchAmbiguous,
testMsgMatchInternalNotFQ)

The checkMsgPath returns the fully qualified path, which replaces the original path in the msgMatchCode.
The location information for each of the individual identifiers in the returned path is the same - the location of the entire original path.

The port of the sender of a message received on a functionalities direct interface can be bound to a constant that is declared inline, and has implicitly the type of port. 
On the other hand, for adversarial and internal messages the sender is known, and its port cannot be bound to a constant.
(checked by: checkPortVarBinding; tested by:
testMsgMatchBindingPortVarNonDirIO)
If the senders port was bound to a constant, it gets added to the current scope.

Values of the message parameters can be bound to fresh constants that are defined inline.
The constants may be defined together with a type - the type must match the type of the parameter.
Some of the parameter values can be left unbound by using the underscore.
If the value was bound to a constant, the constant gets added to the current scope.
(checked by: checkMsgContentBindings; tested by:
testMsgMatchBindingOtherMsg,
testMsgMatchBindingWrongParamNo,
testMsgMatchBindingWrongTyp,
testMsgMatchBindingToStateParam)

*)

messageMatchCodes:
	| MATCH; MESSAGE; WITH; mmc=separated_list(PIPE,msgMatchCode); END; { mmc }
	;

msgMatchCode:
	| patternMatch=msgMatch; ARROW; code=instBlock; { {patternMatch=patternMatch; code=code } }

msgMatch:
	| portConst=idL; AT; path=msgPath; tupleMatch=option(tM); { {portVar=Some portConst; path=path; tupleMatch=tupleMatch} }

	| path=msgPath; tupleMatch=option(tM);  { {portVar=None; path=path; tupleMatch=tupleMatch} }


tM:| LPAREN;tm=separated_list(COMMA,matchItem);RPAREN; {tm}

matchItem:
	| id=idL            { Const id         }
	| nt=nameType       { ConstType nt     }
	| l=loc(UNDERSCORE) { Wildcard (loc l) }
msgPath:
	| mtl=separated_nonempty_list(DOT,msgType) { mtl2msgPath mtl }

msgType:
	| mT=idL          { MsgType mT       }
	| l=loc(OTHERMSG) { OtherMsg (loc l) }

(*---------------*)

(*Simulator*)

(*
The simulator uses a basic adversarial interface (to comunicate with an ideal functionality), simulates a real functionality which is parametrized by ideal functionalities, these must implement the direct interfaces as required by the real functionality.
(checked by: checkSimDecl, checkExistsI2SIO, checkIsRealF, checkSimFunParams; tested by:
testSimUsesNonI2SIO,
testSimSimulatesNonRealFun,
testSimWrongParamNumForSimFun,
testSimParamForSimFunNotIdealFun,
testSimWrongParamDirIOForSimFun
)
*)
simDef:
	| SIM; name=idL; USES uses=idL; SIMS sims=idL; params=paramList; body = simCode; { {id=name; uses=uses; sims=sims; simsParamIds=params; body=body } }

(*

The syntax for simulator code is the same as for party code, except that the port of the message sender cannot be bound to a constant in amessage match, since for simulators the sender is always known (it is either adversary or ideal functionality).
However, the simulator code is subject to different requirements.
The checkSimCode function calls getSimComponents to collect all of the components of the functionality.
Since a subfunctionality can be a real functionality, getSimComponents uses recursive call to get components.
The identifier for the component is of type Qid (dlParsedTree.ml) which is a list of identifiers identifying the parents of the component, and the component itself.
The getSimbIOPaths function then constructs all of the paths to basic adversarial interfaces used by the components.
The getSimInternalPorts function then for every component finds its internal ports. The names of the internal ports get prefixed by the identifier of the parent component.
The stateVar record is flagged with "simulator" string which alters the way the send and transition command is checked.

The initial state of the simulator can match only messages received on the interface it uses (interface to ideal functionality).
The message paths of the matched messages must be fully qualified, and only outgoing messages from the interface to ideal functionality, or incoming adversarial messages to one of the components of the real functionality can be matched.
(checked by: checkMessagePathSim; tested by:
testSimInitStateNonI2SMsgMatch,
testSimMsgMatchOutMsg,
testSimMsgMatchI2SInMsg,
testSimMsgMatchRealFunDirIO,
testSimMsgMatchSubFunDirIO,
testSimMsgMatchParamFunDirIO)

Unlike the functionality, the simulator's message match doesn't have to cover all of the possible messages, but it still cannot match a mesage that was covered by a previous match.
(checked by: checkMsgMatchDeltasSim; tested by: testSimMsgMatchAlreadyCovered)

*)
simCode:
	| LBRACE; sdl=list(stateDefSim) RBRACE;{ sdl }
	;

stateDefSim:
	| INITIAL; STATE; name=idL; code=stateCodeSim; 
		{ InitialState   {id=name; params=[]; code=code}     }
	| STATE; name=idL; LPAREN; params=params; RPAREN; code=stateCodeSim;          
		{ FollowingState {id=name; params=params; code=code} }

stateCodeSim:
	| LBRACE; vars = localVarDecls; codes = messageMatchCodesSim; RBRACE; { {vars=vars; mmcodes=codes} }

messageMatchCodesSim:
	| MATCH; MESSAGE; WITH; mmc=separated_list(PIPE,msgMatchCodeSim); END;{ mmc }
	;

msgMatchCodeSim:
	| patternMatch=msgMatchSim; ARROW; code=instBlock; { {patternMatch=patternMatch; code=code } }

msgMatchSim:
	| msg=msgPath; tupleMatch=option(tM); { {portVar=None; path=msg; tupleMatch=tupleMatch} }

(*---------*)



codeBlock:
	| insts=nonempty_list(instruction);		   { insts }

%inline  instruction: x=loc( instruction_u) { x }
instruction_u:
	| i=assignment { i }
	| i=ifthenelse { i }
	| i=decode     { i }
	| i=terminal   { i }

instBlock:
	| LBRACE; is=codeBlock; RBRACE; { is  }

(*
The branching condition in the if-then-else command must be a boolean expression.
(checked by: checkITE; tested by: testITEcondNotBoolean)

The instructions in branches are then checked, and the variables that were initialized in both branches are marked as initialized in the scope (stateVars record)
after the if-then-else command.
(checked by: checkBranches; tested by: testITEInitVarInOneBranch)
*)	
ifthenelse:
	| IF LPAREN;c=expression;RPAREN; tins=instBlock; ift = iftail; { ITE (c,tins,ift) }

iftail:
	| /*empty*/ 		  { None       }
	| ELSE; eins=instBlock; { Some eins  }
	| elif=elifthenelse;	  { Some [elif]}

%inline  elifthenelse: x=loc(elifthenelse_u) { x }
elifthenelse_u:
	| ELIF LPAREN;c=expression;RPAREN; tins=instBlock; ift = iftail { ITE (c,tins,ift) }

(*
Decode command attempts to cast a constant (or variable) of univ type as some other type.
If the cast succeeds, it is matched with the constants defined inline, and one branch is executed,
if the cast results in an error the other branch is executed.
(checked by: checkDecode; tested by: 
testDecodeNonuniv,
testDecodeTupleWrongParamNo)
*)
decode: 
	| DECODE; ex=expression; AS; ty=ty; WITH; PIPE? OK; tM=decM; ARROW; code1=instBlock; PIPE; ERROR; ARROW; code2=instBlock; END;
	{ Decode (ex,ty,tM,code1,code2) }

decM:
	| tM=tM;        {  tM  }
	| mI=matchItem; { [mI] }

(*
There are two instructions for assigning a value to the variable.
Once the variable is assigned a value it is marked as initialized in the scope (stateVars record) of the current branch of execution.

The Assign instruction assigns the value of the expression to the variable.
The expression must have the same type as the variable.
(checked by: checkValAssign, checkTypeAddBinding; tested by:
testValueAssignWrongType,
testValueAssignInternalPortWrongType,
testValueAssignNonexistingVar,
testValueAssignConst)

The Sample instruction samples from a distribution, and assigns the sampled value to a variable.
The expression must have a type of distribution over samples that have the same type as the variable.
(checked by: checkSamplAssign, checkTypeAddBinding; tested by:
testSampleAssignWrongType,
testSampleAssignNotFromDistr)

*)

assignment:
	| vid=idL; ASGVAL; e=expression; SEMICOLON;   { Assign (vid,e) }
	| vid=idL; ASGSAMPLE;e=expression; SEMICOLON; { Sample (vid,e) }

(*
Every branch of the program must end with one of the terminal instructions.
(checked by: checkEndsAreSaTorF; tested by:
testEndsWSaTorFInstAfterF,
testEndsWSaTorFInstAfterSaT,
testEndsWSaTorFNoSaTorF,
testEndsWSaTorFInstAfterITE,
testEndsWSaTorFInstAfterDecode)
*)

terminal:
	| sat=sendAndTransition; DOT; { SendAndTransition sat }
	| FAIL;DOT;                   { Fail                  }

(*
The sendAndTransition command consists of two parts,
the send part which sends a message, and the transition part which changes the state.

The checkSendMsgPath filters the messages in rFbIOPaths record, so that only outgoing direct and adversarial and incomming internal messages are considered for sending.
The checkMsgPath checks if the message path is in the filtered messages. The paths for direct and adversarial messages do not need to be fully qualified if there is no ambiguity, and the checkMsgPath will return the fully qualified path which replaces the original path. (see the comments for checkMsgPath in the documentation of the message match instruction for more details.) If the message is sent by the simulator the scope (stateVars) will contain the "simulator" flag, this enforces the paths to be fully qualified even for adversarial messages.
(checked by: checkSendMsgPath; tested by:
testSendDirectIn,
testSendAdversIn,
testSendInternOut,
testSimSendNotI2SorRealFun,
testSimSendI2SOutMsg,
testSimSendRFDirIO,
testSimSendRFInAdvMsg,
testSimSendNotAdvIOofSubFun,
testSimSendNotOutAdvMsgofSubFun,
testSimSendNotIOofParamFun,
testSimSendNotOutMsgOfParamFun,
testSimSendMsgPathIncomplete
)

Direct messages must have a destination port defined.
(checked by: checkSendDirect; tested by: testSendDirectNoPort)

Adversarial and internal messages cannot have a port defined.
(checked by: checkSendAdversarial, checkSendInternal; tested by:
testSendAdversWithPort, 
testSendInternWithPort)

The parameters of the sent message must have correct type.
(checked by: checkMsgContentValues; tested by:
testSendWrongParamNo,
testSendWrongParamType)

Transition must have parameters that match the signature of the state.
(checked by: checkTransition; tested by:
testTransitionNonExistingState,
testTransitionWrongParamNo,
testTransitionWrongParamType,
testTransitionNoParams,
testTransitionInitialWithParams)
*)
sendAndTransition:
	| SEND; msg=msgInstance; ANDTXT; TRANSITION; state=stateInstance;  { {msg=msg; state=state} }

msgInstance:
	| path=msgPath; LPAREN; tupleInstance=separated_list(COMMA,expression); RPAREN; portVar=option(dest); { {path=path; tupleInstance=tupleInstance; portVar=portVar} }

dest:| AT; pv=idL; { pv }

stateInstance:
	| id=idL; LPAREN; params=separated_list(COMMA,expression); RPAREN; { {id=id; params=Some params} }
	| id=idL; { {id=id; params=None} }

(* -------------------------------------------------------------------- *)
(* Expressions *)

(*
The syntax for expressions and operators is a simplified version of syntax from ecParser.mly of easycrypt.
*)
%inline uniop:
| NOT    { "[!]" }

%inline sbinop:
| EQ    { "="   }
| OR    { "\\/" }
| AND   { "/\\" }
| HAT   { "^"   }
| x=ROP4{  x    }

%inline binop:
| op=sbinop { op    }

%inline  expression: x=loc(expression_u) { x }
expression_u:
	| e = s_expression_u                                { e }
	| f = idL; args = s_expression+                     { App (f,args)     }
	| e1 = expression; op = loc(binop); e2 = expression { App (op,[e1;e2]) }
	| op = loc(uniop); e = expression;                  { App (op,[e])     }
	| ENCODE; e = expression;                           { Enc e            }
(*
The type of expression is evaluated with checkExpression function (dlExpressons.ml).
If the expression is an identifier, it is first checked if it is a name of one of the variables, constants or internal ports.
If it is a variable it must be initialized.
(checked by: checkExprVar (dl.ml) tested by: testExprUsesUnassignedVar)
If the identifier wasn't found among variables,constants or internal ports then it must be a name of a nullary operator.
(checked by: checkExprId, checkNullaryOp; tested by:
testExprNonExistingVarOp,
testExprNaryOpUsedAsNullaryOp)

If the expression is a tuple of expressions, each expression is evaluated, and the resulting type is a Ttuple of expression types.

If the expression is not an identifier or a tuple it is an application of a function or an operator to some arguments or an encode expression.
Encode expression can be applied to a valid expression of any type, and the type of encode expression is univ.
(checked by: checkExpression; tested by:
testExprTupleWrongArity,
testExprEncode)

Arguments to which an operator (or function) are applied must have the correct types and the operator must exist.
There is currently only one built-in operator, "envport" which takes one argument of type port and returns a bool.
If the operator is not a built-in operator it must be one of the operators from the easycrypt environment.

(checked by: checkSig, checkSigTypes; tested by:
testExprNonexistingFun,
testExprWrongArgNo,
testExprWrongArgType,
testExprWrongArgTypeVar) 
*)
%inline  s_expression: x=loc(s_expression_u) { x }
s_expression_u:
	| qid=qid                                              { Id qid   }
	| LPAREN; es=separated_list(COMMA,expression); RPAREN; { Tuple es }

(* -------------------------------------------------------------------- *)




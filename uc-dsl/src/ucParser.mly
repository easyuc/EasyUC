(* Menhir Specification for UC DSL Parser (UcParser module) *)

%{

open EcUtils
open EcLocation
open UcSpec

let to_id (mtid : msg_type) =
  match mtid with
  | MsgType id -> id
  | OtherMsg l ->
      parse_error l "othermsg keyword cannot be followed by '.'"

let rec r_mtl2msg_path (mtl : msg_type list) (mp : msg_path)=
  match mtl with
  | [] ->
      raise
      (Failure "Cannot happen : empty list when converting mtl to msg_path")
  | [x] -> {io_path = mp.io_path; msg_type = x}
  | hd :: tl ->
      r_mtl2msg_path tl
      {io_path = mp.io_path @ [to_id hd]; msg_type = mp.msg_type}

let mtl2msg_path (mtl : msg_type list) =
  r_mtl2msg_path mtl {io_path=[]; msg_type=OtherMsg _dummy}

(* check for parse errors in messages of direct or adversarial
   interfaces due to improper inclusion of omission of source or
   destination ports *)

let check_parsing_direct_io (io : io) =
  let check_msg msg =
    match msg.port_label with
    | None   ->
        let is_in =
          match msg.direction with
          | In  -> true
          | Out -> false in
        parse_error
        (loc msg.id)
        ((if is_in then "input" else "output") ^
         " messages of direct interfaces must have " ^
         (if is_in then "source" else "destination") ^
         " ports")
    | Some _ -> () in
  match io.body with
  | Basic msgs -> List.iter check_msg msgs
  | Composite _ ->
      (* no parse errors are possible, but there may be type errors *)
      ()

let check_parsing_adversarial_io (io : io) =
  let check_msg msg =
    match msg.port_label with
    | None    -> ()
    | Some id ->
        let is_in =
          match msg.direction with
          | In  -> true
          | Out -> false in
        parse_error
        (loc id)
        ((if is_in then "input" else "output") ^
         " messages of adversarial interfaces cannot have " ^
         (if is_in then "source" else "destination") ^
         " ports") in
  match io.body with
  | Basic msgs -> List.iter check_msg msgs
  | Composite _ ->
      (* no parse errors are possible, but there may be type errors *)
      ()

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

(* Operators and their associativity are copied from EcParser of
   EasyCrypt project. UcLexer contains code for recognizing
   operators. The operators and code are currently a small subset of
   what can be found in EasyCrypt. *)

%right    OR
%right    AND
%nonassoc NOT
%nonassoc EQ 
%left   HAT
%right ROP4

%nonassoc ENCODE

(* The input for the UcParser is a list of tokens produced by UcLexer
   from the UC DSL file.  This list is parsed by UcParser, starting
   with the initial production spec.  The output of UcParser is a
   record of spec type (defined in UcSpec). *)

(* In the generated ucParser.ml : 

val spec : (Lexing.lexbuf -> UcParser.token) -> Lexing.lexbuf -> UcSpec.spec *)

%start <UcSpec.spec> spec

%%

%inline loc(X) : 
  | x = X {
      { pl_desc = x;
        pl_loc  = EcLocation.make $startpos $endpos;
     }
   }

%inline id_l : 
  | id_l = loc(ID)
      { id_l }

%inline qid : 
  | qid = separated_nonempty_list(DOT, id_l)
      { qid }

(* UC DSL specification consists of a preamble which references other
  .ec and .uc files, and a list of definitions of direct and adversarial
  interfaces, functionalities and simlators. *)

spec : 
  | ext = preamble; defs = list(def); EOF
      { {externals = ext; definitions = defs} }
        
preamble : 
  | reqs = option(reqs); imps = option(imps)
      { {ec_requirements = reqs |? [];
         dl_imports      = imps |? []} }

(* Importing is supposed to load content from other .uc files - not
   yet implemented *)

imps: 
  | IMPORT imps = nonempty_list(id_l) DOT
      { imps }

(* requires references EasyCrypt files, these are loaded by
   load_ec_reqs (UcTypecheck) which calls require_import
   (UcEcInterface) which executes an "import require" EasyCrypt
   command.  This loads the content of the .ec theory in the EasyCrypt
   environment which is later queried for types and operators *)

reqs : 
  | REQUIRES reqs = nonempty_list(id_l) DOT
      { reqs }

(* A definition is either a definition of an interface, a
   functionality or a simulator.  All of the names must be distinct
   (checked by check_defs in UcTypecheck, tested by
   testDuplicateIdInIODefinitions, testRealFunIdSameAsIOid,) *)

def : 
  | iod = io_def
      { IODef iod }
  | fund = fun_def
      { FunDef fund }
  | simd = sim_def
      { SimDef simd }

(* Interfaces *)

(* An interface can either be direct or adversarial. They have almost
   the same form. Both have two forms: basic, consisting of a nonempty
   sequence of input and output messages; or composite, consisting of
   a nonempty sequence of named subinterfaces. In direct interfaces,
   input messages must have source ports (but may not have destination
   ports), whereas output messages must have destination ports (but
   may not have source ports). In adversarial interfaces, neither
   input nor output messages may have source or target ports.  The
   names of message parameters as well as the names of source and
   destination ports should be considered documentation *)

io_def : 
  | DIRIO; io = io
      { check_parsing_direct_io io;
        DirectIO io }
  | ADVIO; io = io
      { check_parsing_adversarial_io io;
        AdversarialIO io }

io : 
  | name = id_l; LBRACE; iob = io_body; RBRACE
      { {id = name; body = iob} : io }

io_body : 
  | iob = nonempty_list(message_def)
      { Basic iob }
  | iob = nonempty_list(io_item)
      { Composite iob }

message_body :
  | name = id_l; LPAREN; cont = params; RPAREN
      { {id = name; content = cont} : message_body }

message_def :
  | IN; mb = message_body
      { {direction = In; id = (mb : message_body).id; content = mb.content;
         port_label = None} : message_def }
  | IN; pl = id_l; AT; mb = message_body
      { {direction = In; id = (mb : message_body).id; content = mb.content;
         port_label = Some pl} }
  | OUT; mb = message_body
      { {direction = Out; id = (mb : message_body).id; content = mb.content;
         port_label = None} }
  | OUT; mb = message_body; AT; pl = id_l
      { {direction = Out; id = (mb : message_body).id; content = mb.content;
         port_label = Some pl} }

params : 
  | ps = separated_list(COMMA, name_type) { ps }

io_item :
  | name = id_l; COLON; io_type = id_l { {id = name; io_id = io_type} }

(* Functionalities *)

(* Functionalities are checked by check_funs function (UcTypecheck)
   There are two different types of functionalities - real and ideal.
   For both of them the implemented interfaces must exist, and the
   direct interface must be composite.  An ideal functionality must
   implement a basic adversarial interface, while a real functionality
   can optionally implement a composite adversarial interface.

  (checked by : check_fun_decl; tested by :
  testRealFunImplements2DirIOs, testRealFunImplements2AdvIOs,
  testIdealFunImplements2DirIOs, testIdealFunImplements2AdvIOs,
  testIdealFunImplementsCompositeAdvIO)

  A real functionality can have parameters which is a list of name :
  interface pairs.  The parameter names are unique and interfaces are
  direct and composite (and thus can be implemented by a
  functionality).

  (checked by : check_real_fun_params tested by :
  testRealFunParamIONonExisting, testRealFunParamIdNotUnique,
  testRealFunParamIONotComposite, testRealFunParamIOAdversarial) *)

fun_def :        
  | FUNCT; name = id_l; parameters = fun_params; IMPLEM;
    dir_io = id_l; adv_io = option(id_l); rf_body = real_fun_body
      { {id = name; params = parameters; id_dir_io = dir_io;
         id_adv_io = adv_io; body = rf_body; state_body=[]} }
  | FUNCT; name = id_l; LPAREN; RPAREN; IMPLEM; dir_io = id_l;
    adv_io = option(id_l); rf_body = real_fun_body
      { {id = name; params=[]; id_dir_io = dir_io; id_adv_io = adv_io;
         body = rf_body; state_body=[]} }
  | FUNCT; name = id_l; LPAREN; RPAREN; IMPLEM; dir_io = id_l;
    adv_io = option(id_l); if_body = party_code
      { {id = name; params=[]; id_dir_io = dir_io; id_adv_io = adv_io;
         body=[]; state_body = if_body} }

fun_params : 
  | LPAREN; fps = separated_nonempty_list(COMMA, fun_param); RPAREN
      { fps }

fun_param : 
  | name = id_l; COLON; id_dir_io = id_l
      { {id = name; id_dir_io = id_dir_io} : fun_param }

real_fun_body : 
  | LBRACE; sil = nonempty_list(sub_item); RBRACE
      { sil }

(* The body of a real functionality consists of subfunctionalities and
   parties. Their names must be unique and different from the names of
   the parameters.  The subfunctionality must have a type of an
   existing functionality, and it's parameters must be other
   subfunctionalities and parameters.

   (checked by check_sub_fun_decl, check_fun_decl; tested by :
   testSubFunNonExistingFun, testDuplicateSubFunId,
   testSubFunIdSameAsParamId)

   Once the declarations of all functionalities are checked, the
   subfunctionalities are further checked by for circular references
   (a functionality cannot be its own subfunctionality),

   (checked by check_circ_refs_in_r_funs; tested by :
   testCircFunRefSingleStep, testCircFunRefTwoSteps )

   and the prameters are checked to match the direct interface types
   of subfunctionality.

   (checked by check_sub_fun_params; tested by :
   testSubFunRFWrongParamNo, testSubFunRFWrongParamTypeIF,
   testSubFunRFWrongParamTypeRF, testSubFunRFWrongParamTypeParam,
   testSubFunIdSameAsParamId) *)

sub_item : 
  | sfd = sub_fun_decl
      { SubFunDecl sfd }
  | pd  = party_def
      { PartyDef pd }

sub_fun_decl : 
  | SUBFUN; name = id_l; EQ; fun_name = id_l; params = param_list
      { {id = name; fun_id = fun_name; fun_param_ids = params} : sub_fun_decl }

param_list : 
  | LPAREN; params = separated_list(COMMA, id_l); RPAREN
      { params }

(* The party serves exactly one basic direct interface that is a
   component of th e composite direct interface implemented by the
   functionality; the party serves at most one basic adversarial
   direct interface hat is a component of the composite adversarial
   interface implemented by the functionality.

   (checked by : check_party_decl; tested by :
   testPartyServesDeclNoDirIO, testPartyServesDeclTwoDirIO,
   testPartyServesDeclIOItemNotASubIO, testPartyServesDeclNotInDirIO,
   testPartyServesDeclMultipleInIOs)

   The parties can't serve the same basic interfaces, and the union of
   the basic interfaces served by the parties sums up to composite
   interfaces implemented by the functionality.  (checked by :
   check_parties_serve_direct_sum; tested by : testPartiesServeSameIO,
   testPartiesDontServeEntireDirIO, testPartiesDontServeEntireAdvIO) *)

party_def : 
  | PARTY; name = id_l; serves = serves; code = party_code
     { {id = name; serves = serves; code = code} }

serves : 
  | SERVES; sl = separated_list(COMMA, qid)
      { sl }

party_code : 
  | LBRACE; sdl = nonempty_list(state_def) RBRACE
      { sdl }

(* The party code consists of a list of states.  The states must have
   unique names, and there must be exactly one initial state.
   (checked by : check_states; tested by : testPartyNoInitialState,
   testPartyMultipleInitialStates, testPartyDuplicateStateId )

   Individual state's parameters and variables must have unique names
   and their types must exist.  (checked by : check_state_decl,
   check_params; tested by : testStateParamsDuplicateIds,
   testStateParamsNonExistingType, testStateParamNonExistingType,
   testStateVarsDuplicateIds, testStateVarParamDuplicateIds,
   testStateVarsNonExistingType, testStateVarNonExistingType) *)

state_def : 
  | INITIAL; STATE; name = id_l; code = state_code
      { InitialState   {id = name; params=[]; code = code}  }
  | STATE; name = id_l; LPAREN; params = params; RPAREN; code = state_code
      { FollowingState {id = name; params = params; code = code} }

state_code : 
  | LBRACE; vars = local_var_decls; codes = message_match_codes; RBRACE
      { {vars = vars; mmcodes = codes} }

local_var_decls : 
  | lvds = list(local_var_decl)
      { List.flatten lvds }

local_var_decl : 
  | VAR; lvs = nonempty_list (id_l); COLON; t = ty SEMICOLON
      { List.map (fun lv -> {id = lv; ty = t}) lvs }

(* Incomming messages are matched against a list of possible messages
   contained in a r_fb_io_paths record.  This record contains three
   fields : direct, adversarial and internal, each field is a list of
   b_io_paths, and a b_io_path is a pair of a string list (a path) and
   a basic interface.  For a party (or an ideal functionality) the
   r_fb_io_paths record is constructed in check_party_code function,
   by making calls to get_r_fb_io_paths (or get_fb_io_paths) function.

   The r_fb_io_paths for a party will contain a single path for the
   basic direct interface the party is serving, a single path for the
   basic adversarial interface the party is serving (or empty list if
   the party doesn't serve adversarial interface) and every component
   of the direct interface implemented by a subfunctionality or
   functionalities parameter will have a b_io_path in the internal
   field of the r_fb_io_paths record.

  The internal field of a r_fb_io_path record for an ideal
  functionality will be an empty list, the adversarial field will
  contain a single path to the adversarial interface of the
  functionality, and the direct field will contain a path for each of
  the components of the composite interface implemented by the
  functionality.

  The code of the state consists of a single match message statement
  containing a list of possible message matches together with the list
  of statements handling the matched message.

  The match consists of a message path followed by the message type
  and an optional binding of message parameters to local constants.
  The message path is a sequence of strings, starting with the
  component (subfunctionality or parameter) name (or empty string if
  the component is the functionality itself), followed by the name of
  the implemented interface, followed by the component of the
  interface.  The message type can be a message from the basic
  interface or "othermsg" keyword covering all the messages contained
  in the path.  The message path doesn't have to be complete when
  "othermsg" is used, e.g. component_name.othermsg will match against
  all of the messages comming from that component of the functionality
  and just othermsg will match against all messages.

  The check_state function initializes the state_vars record - it
  contains the information about current scope.  Initially it contains
  the state parameters as constants, state variables as uninitialized
  variables, and names of parties, subfunctionalities and parameters
  as internal ports. These can be used in code as constants of type
  port.  Furthermore, the signatures of all of the states of the party
  are collected, a signature is a typ list containing the types of the
  state parameters.  These signatures are used to check transitioning
  to a state.

  The check_state_code function calls check_m_mcode on every message
  match, and the entire match message statement is checked to ensure
  all of the messages are matched, and that every match is not covered
  by a previous match.  (checked by check_msg_match_deltas; tested by
  : testMsgMatchAlreadyCovered, testMsgMatchIncomplete,
  testIdealFunMsgMatchIncomplete)

  The check_message_path function filters the r_fb_io_paths record so
  that the basic interfaces contain only messages the party can
  receive; these are the incomming messages of the direct and
  adversarial fields, and the outgoing messages from the internal
  field of the rfb_io_paths.  The paths of the messages do not need to
  be fully qualified if there is no ambiguity- they can contain only
  message type instead of the full path (e.g. just message_type_name
  instead of composite_i_oname.component_name.message_type_name) or
  just the basic interface name followed by the message type
  (e.g. component_name.message_type_name instead of
  composite_i_oname.component_name.message_type_name).  When matching
  internal messages, the fully qualified path must be used.

  (checked by : check_msg_path; tested by : testMsgMatchUnexpected,
  testMsgMatchAmbiguous, testMsgMatchInternalNotFQ)

  The check_msg_path returns the fully qualified path, which replaces
  the original path in the msg_match_code.  The location information
  for each of the individual identifiers in the returned path is the
  same - the location of the entire original path.

  The port of the sender of a message received on a functionalities
  direct inter face can be bound to a constant that is declared
  inline, and has implicitly the type of port.  On the other hand, for
  adversarial and internal messages the sender is known, and its port
  cannot be bound to a constant.

  (checked by : check_port_var_binding; tested by :
  testMsgMatchBindingPortVarNonDirIO) If the senders port was bound to
  a constant, it gets added to the current scope.

  Values of the message parameters can be bound to fresh constants
  that are defined inline.  The constants may be defined together with
  a type - the type must match the type of the parameter.  Some of the
  parameter values can be left unbound by using the underscore.  If
  the value was bound to a constant, the constant gets added to the
  current scope.

  (checked by : check_msg_content_bindings; tested by :
  testMsgMatchBindingOtherMsg, testMsgMatchBindingWrongParamNo,
  testMsgMatchBindingWrongTyp, testMsgMatchBindingToStateParam) *)

message_match_codes : 
  | MATCH; MESSAGE; WITH; mmc = separated_list(PIPE, msg_match_code); END
     { mmc }

msg_match_code : 
  | pattern_match = msg_match; ARROW; code = inst_block
      { {pattern_match = pattern_match; code = code } }

msg_match : 
  | port_const = id_l; AT; path = msg_path; tuple_match = option(t_m)
      { {port_var = Some port_const; path = path; tuple_match = tuple_match} }

  | path = msg_path; tuple_match = option(t_m)
      { {port_var = None; path = path; tuple_match = tuple_match} }

t_m :
  | LPAREN; tm = separated_list(COMMA, match_item); RPAREN
      {tm}

match_item : 
  | id = id_l
      { Const id }
  | nt = name_type
      { ConstType nt }
  | l = loc(UNDERSCORE)
      { Wildcard (loc l) }

msg_path : 
  | mtl = separated_nonempty_list(DOT, msg_type)
      { mtl2msg_path mtl }

msg_type : 
  | m_t = id_l
      { MsgType m_t }
  | l = loc(OTHERMSG)
      { OtherMsg (loc l) }

(*Simulator*)

(* The simulator uses a basic adversarial interface (to comunicate
   with an ideal functionality), simulates a real functionality which
   is parametrized by ideal functionalities, these must implement the
   direct interfaces as required by the real functionality.  (checked
   by : check_sim_decl, check_exists_i2_sio, check_is_real_f,
   check_sim_fun_params; tested by : testSimUsesNonI2SIO,
   testSimSimulatesNonRealFun, testSimWrongParamNumForSimFun,
   testSimParamForSimFunNotIdealFun, testSimWrongParamDirIOForSimFun) *)

sim_def : 
  | SIM; name = id_l; USES uses = id_l; SIMS sims = id_l;
    params = param_list; body = sim_code
      { {id = name; uses = uses; sims = sims; sims_param_ids = params;
         body = body } }

(* The syntax for simulator code is the same as for party code, except
   that the port of the message sender cannot be bound to a constant
   in amessage match, since for simulators the sender is always known
   (it is either adversary or ideal functionality).  However, the
   simulator code is subject to different requirements.  The
   check_sim_code function calls get_sim_components to collect all of
   the components of the functionality.  Since a subfunctionality can
   be a real functionality, get_sim_components uses recursive call to
   get components.  The identifier for the component is of type Qid
   (UcTypedSpec) which is a list of identifiers identifying the
   parents of the component, and the component itself.  The
   get_simb_io_paths function then constructs all of the paths to
   basic adversarial interfaces used by the components.  The
   get_sim_internal_ports function then for every component finds its
   internal ports. The names of the internal ports get prefixed by the
   identifier of the parent component.  The state_var record is
   flagged with "simulator" string which alters the way the send and
   transition command is checked.

   The initial state of the simulator can match only messages received
   on the interface it uses (interface to ideal functionality).  The
   message paths of the matched messages must be fully qualified, and
   only outgoing messages from the interface to ideal functionality,
   or incoming adversarial messages to one of the components of the
   real functionality can be matched.

   (checked by : check_message_path_sim; tested by :
   testSimInitStateNonI2SMsgMatch, testSimMsgMatchOutMsg,
   testSimMsgMatchI2SInMsg, testSimMsgMatchRealFunDirIO,
   testSimMsgMatchSubFunDirIO, testSimMsgMatchParamFunDirIO)

   Unlike the functionality, the simulator's message match doesn't
   have to cover all of the possible messages, but it still cannot
   match a mesage that was covered by a previous match.

  (checked by : check_msg_match_deltas_sim; tested by :
  testSimMsgMatchAlreadyCovered) *)

sim_code : 
  | LBRACE; sdl = list(state_def_sim) RBRACE
      { sdl }

state_def_sim : 
  | INITIAL; STATE; name = id_l; code = state_code_sim
      { InitialState {id = name; params=[]; code = code} }
  | STATE; name = id_l; LPAREN; params = params; RPAREN; code = state_code_sim
      { FollowingState {id = name; params = params; code = code} }

state_code_sim : 
  | LBRACE; vars = local_var_decls; codes = message_match_codes_sim; RBRACE
      { {vars = vars; mmcodes = codes} }

message_match_codes_sim : 
  | MATCH; MESSAGE; WITH; mmc = separated_list(PIPE, msg_match_code_sim); END
      { mmc }

msg_match_code_sim : 
  | pattern_match = msg_match_sim; ARROW; code = inst_block
      { {pattern_match = pattern_match; code = code } }

msg_match_sim : 
  | msg = msg_path; tuple_match = option(t_m)
      { {port_var = None; path = msg; tuple_match = tuple_match} }

code_block : 
  | insts = nonempty_list(instruction)
      { insts }

%inline instruction :
  | x = loc(instruction_u)
      { x }

instruction_u : 
  | i = assignment
      { i }
  | i = ifthenelse
      { i }
  | i = decode
      { i }
  | i = terminal
      { i }

inst_block : 
  | LBRACE; is = code_block; RBRACE
      { is }

(* The branching condition in the if-then-else command must be a
   boolean expression.  (checked by : check_ite; tested by :
   test_it_econd_not_boolean)

   The instructions in branches are then checked, and the variables
   that were initialized in both branches are marked as initialized in
   the scope (state_vars record) after the if-then-else command.
   (checked by : check_branches; tested by :
   test_ite_init_var_in_one_branch) *)

ifthenelse : 
  | IF LPAREN; c = expression;RPAREN; tins = inst_block; ift = iftail
      { ITE (c, tins, ift) }

iftail : 
  | /*empty*/
      { None }
  | ELSE; eins = inst_block
      { Some eins }
  | elif = elifthenelse
      { Some [elif] }

%inline elifthenelse :
  | x = loc(elifthenelse_u)
      { x }

elifthenelse_u : 
  | ELIF LPAREN; c = expression;RPAREN; tins = inst_block; ift = iftail
      { ITE (c, tins, ift) }

(* Decode command attempts to cast a constant (or variable) of univ
   type as some other type.  If the cast succeeds, it is matched with
   the constants defined inline, and one branch is executed, if the
   cast results in an error the other branch is executed.

   (checked by : check_decode; tested by : testDecodeNonuniv,
   testDecodeTupleWrongParamNo) *)

decode : 
  | DECODE; ex = expression; AS; ty = ty; WITH; PIPE? OK;
    t_m = dec_m; ARROW; code1 = inst_block; PIPE; ERROR; ARROW;
    code2 = inst_block; END;
      { Decode (ex, ty, t_m, code1, code2) }

dec_m : 
  | t_m = t_m
      { t_m }
  | m_i = match_item
      { [m_i] }

(* There are two instructions for assigning a value to the variable.
   Once the variable is assigned a value it is marked as initialized
   in the scope (state_vars record) of the current branch of
   execution.

   The Assign instruction assigns the value of the expression to the
   variable.  The expression must have the same type as the variable.
   (checked by : check_val_assign, check_type_add_binding; tested by :
   testValueAssignWrongType, testValueAssignInternalPortWrongType,
   testValueAssignNonexistingVar, testValueAssignConst)

   The Sample instruction samples from a distribution, and assigns the
   sampled value to a variable.  The expression must have a type of
   distribution over samples that have the same type as the variable.

   (checked by : check_sampl_assign, check_type_add_binding; tested by
   : testSampleAssignWrongType, testSampleAssignNotFromDistr) *)

assignment : 
  | vid = id_l; ASGVAL; e = expression; SEMICOLON
      { Assign (vid, e) }
  | vid = id_l; ASGSAMPLE; e = expression; SEMICOLON
      { Sample (vid, e) }

(* Every branch of the program must end with one of the terminal instructions.

   (checked by : check_ends_are_sa_tor_f; tested by :
   testEndsWSaTorFInstAfterF, testEndsWSaTorFInstAfterSaT,
   testEndsWSaTorFNoSaTorF, testEndsWSaTorFInstAfterITE,
   testEndsWSaTorFInstAfterDecode) *)

terminal : 
  | sat = send_and_transition; DOT
      { SendAndTransition sat }
  | FAIL; DOT
      { Fail }

(* The send_and_transition command consists of two parts, the send
   part which sends a message, and the transition part which changes
   the state.

  The check_send_msg_path filters the messages in r_fb_io_paths
  record, so that only outgoing direct and adversarial and incomming
  internal messages are considered for sending.  The check_msg_path
  checks if the message path is in the filtered messages. The paths
  for direct and adversarial messages do not need to be fully
  qualified if there is no ambiguity, and the check_msg_path will
  return the fully qualified path which replaces the original
  path. (see the comments for check_msg_path in the documentation of
  the message match instruction for more details.) If the message is
  sent by the simulator the scope (state_vars) will contain the
  "simulator" flag, this enforces the paths to be fully qualified even
  for adversarial messages.  (checked by : check_send_msg_path; tested
  by : testSendDirectIn, testSendAdversIn, testSendInternOut,
  testSimSendNotI2SorRealFun, testSimSendI2SOutMsg,
  testSimSendRFDirIO, testSimSendRFInAdvMsg,
  testSimSendNotAdvIOofSubFun, testSimSendNotOutAdvMsgofSubFun,
  testSimSendNotIOofParamFun, testSimSendNotOutMsgOfParamFun,
  testSimSendMsgPathIncomplete)

  Direct messages must have a destination port defined.  (checked by :
  check_send_direct; tested by : testSendDirectNoPort)

  Adversarial and internal messages cannot have a port defined.
  (checked by : check_send_adversarial, check_send_internal; tested by
  : testSendAdversWithPort, testSendInternWithPort)

  The parameters of the sent message must have correct type.  (checked
  by : check_msg_content_values; tested by : testSendWrongParamNo,
  testSendWrongParamType)

  Transition must have parameters that match the signature of the
  state.  (checked by : check_transition; tested by :
  testTransitionNonExistingState, testTransitionWrongParamNo,
  testTransitionWrongParamType, testTransitionNoParams,
  testTransitionInitialWithParams) *)

send_and_transition : 
  | SEND; msg = msg_instance; ANDTXT; TRANSITION; state = state_instance
      { {msg = msg; state = state} }

msg_instance : 
  | path = msg_path; LPAREN;
    tuple_instance = separated_list(COMMA, expression); RPAREN;
    port_var = option(dest)
      { {path = path; tuple_instance = tuple_instance; port_var = port_var} }

dest :
  | AT; pv = id_l
      { pv }

state_instance : 
  | id = id_l; LPAREN; params = separated_list(COMMA, expression); RPAREN
      { {id = id; params = Some params} }
  | id = id_l
      { {id = id; params = None} }

(* Types *)

(* The typ type is a simplified version of ty type from EcTypes, for
   more info on what was removed from ec_types look at documentation
   in UcTypes. *)

name_type : 
  | name = id_l; COLON; t = ty; { {id = name; ty = t} : name_type }

ty : 
  | name = id_l
      { NamedTy name }
  | tuphd = ty_br; STAR; tuptl = separated_nonempty_list(STAR, ty_br)
      { TupleTy (tuphd :: tuptl) }

ty_br : 
  | name = id_l
      { NamedTy name }
  | LPAREN; tuphd = ty_br; STAR;
    tuptl = separated_nonempty_list(STAR, ty_br); RPAREN
      { TupleTy (tuphd :: tuptl) }

(* Expressions *)

(* The syntax for expressions and operators is a simplified version of
   syntax from EcParser of EasyCrypt. *)

%inline uniop : 
  | NOT
      { "[!]" }

%inline sbinop : 
  | EQ
      { "=" }
  | OR
      { "\\/" }
  | AND
      { "/\\" }
  | HAT
      { "^" }
  | x = ROP4
      {  x }

%inline binop : 
  | op = sbinop
      { op }

%inline expression :
  | x = loc(expression_u)
      { x }

expression_u : 
  | e = s_expression_u
     { e }
  | f = id_l; args = s_expression+
     { App (f, args) }
  | e1 = expression; op = loc(binop); e2 = expression
     { App (op,[e1; e2]) }
  | op = loc(uniop); e = expression
     { App (op,[e]) }
  | ENCODE; e = expression
     { Enc e }

(* The type of expression is evaluated with check_expression function
   (UcExpressons).  If the expression is an identifier, it is first
   checked if it is a name of one of the variables, constants or
   internal ports.  If it is a variable it must be initialized.
   (checked by : check_expr_var (UcTypecheck) tested by :
   testExprUsesUnassignedVar) If the identifier wasn't found among
   variables, constants or internal ports then it must be a name of a
   nullary operator.

   (checked by : check_expr_id, check_nullary_op; tested by :
   testExprNonExistingVarOp, testExprNaryOpUsedAsNullaryOp)

   If the expression is a tuple of expressions, each expression is
   evaluated, and the resulting type is a Ttuple of expression types.

   If the expression is not an identifier or a tuple it is an
   application of a function or an operator to some arguments or an
   encode expression.  Encode expression can be applied to a valid
   expression of any type, and the type of encode expression is univ.

   (checked by : check_expression; tested by :
   testExprTupleWrongArity, testExprEncode)

   Arguments to which an operator (or function) are applied must have
   the correct types and the operator must exist.  There is currently
   only one built-in operator, "envport" which takes one argument of
   type port and returns a bool.  If the operator is not a built-in
   operator it must be one of the operators from the EasyCrypt
   environment.

  (checked by : check_sig, check_sig_types; tested by :
  testExprNonexistingFun, testExprWrongArgNo, testExprWrongArgType,
  testExprWrongArgTypeVar) *)

%inline s_expression :
  | x = loc(s_expression_u)
      { x }

s_expression_u : 
  | qid = qid
      { Id qid }
  | LPAREN; es = separated_list(COMMA, expression); RPAREN
      { Tuple es }

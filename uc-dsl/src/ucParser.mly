(* Menhir Specification for UC DSL Parser (UcParser module) *)

%{

open EcUtils
open EcLocation
open UcSpec
open UcMessage

let to_id (mpi : msg_path_item) =
  match mpi with
  | MsgPathId id      -> id
  | MsgPathOtherMsg l ->
      parse_error l "othermsg keyword cannot be followed by \".\""

let rec to_msg_path (mpis : msg_path_item list) (mp : msg_path) =
  match mpis with
  | []       ->
      failure "cannot happen: empty list when converting mpis to msg_path"
  | [x]      -> {inter_id_path = mp.inter_id_path; msg_or_other = x}
  | hd :: tl ->
      to_msg_path tl
      {inter_id_path = mp.inter_id_path @ [to_id hd];
       msg_or_other = mp.msg_or_other}

let msg_path_items_to_msg_path (mpis : msg_path_item list) =
  to_msg_path mpis
  {inter_id_path = []; msg_or_other = MsgPathOtherMsg _dummy}

(* check for parse errors in messages of direct or adversarial
   interfaces due to improper inclusion of omission of source or
   destination ports *)

let check_parsing_direct_inter (ni : named_inter) =
  let check_msg msg =
    match msg.port with
    | None   ->
        let is_in =
          match msg.dir with
          | In  -> true
          | Out -> false in
        parse_error
        (loc msg.id)
        ((if is_in then "input" else "output") ^
         " messages of direct interfaces must have " ^
         (if is_in then "source" else "destination") ^
         " ports")
    | Some _ -> () in
  match ni.inter with
  | Basic msgs -> List.iter check_msg msgs
  | Composite _ ->
      (* no parse errors are possible, but there may be type errors *)
      ()

let check_parsing_adversarial_inter (ni : named_inter) =
  let check_msg msg =
    match msg.port with
    | None    -> ()
    | Some id ->
        let is_in =
          match msg.dir with
          | In  -> true
          | Out -> false in
        parse_error
        (loc id)
        ((if is_in then "input" else "output") ^
         " messages of adversarial interfaces cannot have " ^
         (if is_in then "source" else "destination") ^
         " ports") in
  match ni.inter with
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
%token DIRECT
%token ADVERSARIAL
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
%token UC_REQUIRES
%token EC_REQUIRES
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

(* operators and their associativity are copied from EcParser of
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

(* the input for the UcParser is a list of tokens produced by UcLexer
   from the UC DSL file.  This list is parsed by UcParser, starting
   with the initial production spec.  The output of UcParser is a
   record of spec type (defined in UcSpec). *)

(* in the generated ucParser.ml : 

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

(* a UC DSL specification consists of a preamble which references
  other .ec and .uc files, and a list of definitions of direct and
  adversarial interfaces, functionalities and simlators. *)

spec : 
  | ext = preamble; defs = list(def); EOF
      { {externals = ext; definitions = defs} }
        
preamble : 
  | ec_reqs = option(ec_requires); uc_reqs = option(uc_requires)
      { {ec_requires = ec_reqs |? [];
         uc_requires = uc_reqs |? []} }

(* require .uc files - not yet implemented *)

uc_requires : 
  | UC_REQUIRES uc_reqs = nonempty_list(id_l) DOT
      { uc_reqs }

(* require import .ec files, making types and operators available
   for use in UC DSL specification *)

ec_requires : 
  | EC_REQUIRES ec_reqs = nonempty_list(id_l) DOT
      { ec_reqs }

(* a definition is either a definition of an interface, a
   functionality or a simulator.  All of the names must be
   distinct. *)

def : 
  | ind = inter_def
      { InterDef ind }
  | fund = fun_def
      { FunDef fund }
  | simd = sim_def
      { SimDef simd }

(* Functionality Interfaces *)

(* an interface can either be direct (governing messages that are
   input from or output to the environment (or a parent
   functionality); or adversarial (governing messages that are input
   from or output to the adversary (or a simulator)). They have almost
   the same form. Both have two forms: basic, consisting of a nonempty
   sequence of input and output messages; or composite, consisting of
   a nonempty sequence of named subinterfaces. Mesages have typed
   parameters; when the list of parameters is empty, the "()" may be
   omitted.  In direct interfaces, input messages must have source
   ports (but may not have destination ports), whereas output messages
   must have destination ports (but may not have source ports). In
   adversarial interfaces, neither input nor output messages may have
   source or target ports. The names of message parameters as well as
   the names of source and destination ports should be considered
   documentation *)

inter_def : 
  | DIRECT; ni = named_inter
      { check_parsing_direct_inter ni;
        DirectInter ni }
  | ADVERSARIAL; ni = named_inter
      { check_parsing_adversarial_inter ni;
        AdversarialInter ni }

named_inter : 
  | inter_id = id_l; LBRACE; inter = option(inter); RBRACE
      { match inter with
        | None       ->
            parse_error (loc inter_id) "interfaces may not be empty"
        | Some inter ->
            {id = inter_id; inter = inter} : named_inter }

inter : 
  | msgs = nonempty_list(message_def)
      { Basic msgs }
  | cis = nonempty_list(comp_item)
      { Composite cis }

message_def :
  | IN; mb = message_body
      { {dir = In; id = (mb : message_body).id; params = mb.params;
         port = None} : message_def }
  | IN; pt = id_l; AT; mb = message_body
      { {dir = In; id = (mb : message_body).id; params = mb.params;
         port = Some pt} }
  | OUT; mb = message_body
      { {dir = Out; id = (mb : message_body).id; params = mb.params;
         port = None} }
  | OUT; mb = message_body; AT; pt = id_l
      { {dir = Out; id = (mb : message_body).id; params = mb.params;
         port = Some pt} }

message_body :
  | msg_id = id_l; params = option(message_params)
      { let params = params |? [] in
        {id = msg_id; params = params} : message_body }

message_params :
  LPAREN; params = type_bindings; RPAREN
    { params }

comp_item :
  | sub_id = id_l; COLON; inter_id = id_l
      { {sub_id = sub_id; inter_id = inter_id} }

(* Functionalities *)

(* A functionality has a name, parameter list, an implementation
   specification, and a body.

   Parameters are functionalities that implement the specified
   composite direct interfaces. Parameter lists may be empty, in which
   case the "()" may be omitted. A real functionality may have a
   non-zero number of parameters, but an ideal functionality must have
   no parameters.

   A functionality always implements a composite direct interface
   (listed first), and optionally implements an adversarial interface
   (listed second).  A real functionality either implements no
   adversarial interface, or implements a composite adversarial
   interface. An ideal functionality must implement a basic
   adversarial interface.

   The body of the functionality has a different form depending upon
   whether the functionality is real or ideal. The body of a real
   functionality consists of: an optional list of subfunctionality
   declarations, whose names must be distinct from the functionality's
   parameters, and which represent instances of ideal functionalities;
   followed by a nonempty list of party definitions.

   The body of an ideal functionality is a state machine. *)

fun_def :        
  | FUNCT; name = id_l; params = option(fun_params);
    IMPLEM; dir_id = id_l; adv_id = option(id_l);
    fun_body = fun_body
      { let params = params |? [] in
        let () =
          if not (is_real_fun_body fun_body) && not (List.is_empty params)
          then parse_error (loc name)
               "ideal functionalities may not have parameters"
          else () in
        {id = name; params = params;
         id_dir = dir_id; id_adv = adv_id;
         fun_body = fun_body} }

fun_params : 
  | LPAREN; fps = separated_list(COMMA, fun_param); RPAREN
      { fps }

fun_param : 
  | name = id_l; COLON; id_dir = id_l
      { {id = name; id_dir = id_dir} : fun_param }

fun_body :
  | rfb = real_fun_body
      { FunBodyReal rfb }
  | ifb = ideal_fun_body
      { FunBodyIdeal ifb }

real_fun_body : 
  | LBRACE; sfs = list(sub_fun_decl); pdfs = list(party_def); RBRACE
      { {sub_fun_decls = sfs; party_defs = pdfs} : fun_body_real }

ideal_fun_body :
  | sm = state_machine
      { sm }

(* a subfunctionality declaration declares a new instance
   of an ideal functionality *)

sub_fun_decl : 
  | SUBFUN; id = id_l; EQ; fun_id = id_l;
      { {id = id; fun_id = fun_id} : sub_fun_decl }

(* A functionality party serves exactly one basic direct interface,
   which must be a component of the composite direct interface
   implemented by the functionality; the party serves at most one
   basic adversarial direct interface, which must be a component of
   the composite adversarial interface implemented by the
   functionality. Different parties can't serve the same basic
   interfaces, and the union of the basic interfaces served by the
   parties must sum up to the composite interfaces implemented by the
   functionality. The actions of a party are determined by a state
   machine. *)

party_def : 
  | PARTY; id = id_l; serves = serves; sm = state_machine
     { {id = id; serves = serves; states = sm} }

serves : 
  | SERVES; serves = separated_list(COMMA, qid)
      { serves }

state_machine : 
  | LBRACE; sds = nonempty_list(state_def) RBRACE
      { sds }

(* A state machine consists of a list of named states, which are
   parameterized by typed values. The states must have unique names,
   and there must be exactly one initial state. That initial state
   must take no paramters. A state's code declares local variables,
   and describes how incoming messages should be matched and
   processed via a nonempty list of message matching clauses *)

state_def : 
  | INITIAL; st = state
      { let l = loc((st : state).id) in
        let params = st.params in
        if not (List.is_empty params)
        then parse_error l "an initial state may not have parameters"
        else InitialState {id = st.id; params = []; code = st.code} }
  | st = state
      { FollowingState
        {id = (st : state).id; params = st.params; code = st.code} }

state : 
  | STATE; id = id_l; params = option(state_params); code = state_code
      { let params = params |? [] in
        {id = id; params = params; code = code} : state }

state_params :
  LPAREN; params = type_bindings; RPAREN
    { params }

state_code : 
  | LBRACE; vars = local_var_decls; mm = message_matching; RBRACE
      { {vars = vars; mmclauses = mm} }

local_var_decls : 
  | lvds = list(local_var_decl)
      { List.flatten lvds }

local_var_decl : 
  | VAR; lvs = nonempty_list (id_l); COLON; t = ty SEMICOLON
      { List.map (fun lv -> {id = lv; ty = t}) lvs }

(* Message matching specifies how incoming messages should be
   processed, resulting in a state transition or failure.

   A message path is a "."-separated sequence of identifiers, taking
   us from the name of a composite interface, to the name of one of
   its components, to one of the input messages of the component's
   basic interface.

   The possible message paths are determined by the direct and
   adversarial interfaces implemented by the functionality (restricted
   to the basic interfaces served by the party, in the case of a real
   functionality), plus the direct interfaces of the party's
   subfunctionalities.

   For example, suppose the functionality implements FwDir (and, in
   the case of a real functionality, that the party serves fwDir):

     direct fwDir {
       in pt1@fw_req(pt2 : port, u : univ)
       out fw_rsp(pt1 : port, u : univ)@pt2
     }

     direct FwDir {D : fwDir}

   Then FwDir.D.fwDir is the only valid message path. If there is
   a subfunctionality

     subfun Fw1 = Forw

   where the ideal functionality Forw has FwDir as its direct interface,
   then

     Fw1.D.fw_req

   will be a valid message path.

   Message path patterns look like message paths, except that:

   (1) they may end with the token "othermsg" to match any completion
       of the given path;

   (2) message paths for direct interfaces are prefaced with a
       an identifer id followed by the token "@" - id will become
       bound to the source port of the message being matched;

   (3) when there is no ambiguity, a prefix of a path may be omitted.

   E.g.,

     pt@fw_req
     pt@D.fw_req
     pt@FwDir.D.fw_req

     othermsg
     D.othermsg
     FwDir.D.othermsg

   are valid path patterns given the above definitions.

   A message pattern is then a message path pattern followed by
   an optional tuple of argument patterns. E.g.,

     pt@fw_req(pt' : port, u' : univ)
     pt@D.fw_req(pt' : port, u' : univ)
     pt@FwDir.D.fw_req(pt' : port, u' : univ)

   will match a fw_req message, and in the process pt will be bound
   to its source port, and pt' and u' will be bound to the message
   arguments.

   Finally, a message matching clause consists of a message pattern
   followed by the code to run on a matching message. *)

message_matching : 
  | MATCH; MESSAGE; WITH; PIPE?
    mm = loc(separated_list(PIPE, msg_match_clause)); END
     { if List.is_empty (unloc mm)
       then parse_error (loc mm)
            "at least one message matching clause is required";
       unloc mm }

msg_match_clause : 
  | msg_pat = msg_pat; ARROW; code = inst_block
      { {msg_pat = msg_pat; code = code } }

msg_pat : 
  | port_id = id_l; AT; mmb = msg_pat_body
      { {port_id = Some port_id; path = (mmb : msg_pat_body).path;
         pat_args = mmb.pat_args} }
  | mmb = msg_pat_body
      { {port_id = None; path = (mmb : msg_pat_body).path;
         pat_args = mmb.pat_args} }

msg_pat_body : 
  | path = msg_path; pat_args = option(pat_args)
      { {path = path; pat_args = pat_args} : msg_pat_body }

pat_args :
  | LPAREN; pa = separated_list(COMMA, pat); RPAREN
      { pa }

pat : 
  | id = id_l
      { PatId id }
  | nt = type_binding
      { PatIdType nt }
  | l = loc(UNDERSCORE)
      { PatWildcard (loc l) }

msg_path : 
  | mpis = separated_nonempty_list(DOT, msg_path_item)
      { (* OTHERMSG, if it appears, must be at end *)
        msg_path_items_to_msg_path mpis }

msg_path_item : 
  | id = id_l
      { MsgPathId id }
  | l = loc(OTHERMSG)
      { MsgPathOtherMsg (loc l) }

(* Simulators *)

(* A simulator uses a basic adversarial interface, to communicate with
   an ideal functionality. It simulates a real functionality, applied
   to ideal functionalities (in the case the real functionality is
   parameterized).

   A simulator's state machine is the same as an ordinary state
   machine, except that the source port isn't bound in a message
   pattern, since for simulators the sender is always known (it is
   either adversary or ideal functionality).

   The initial state of the simulator can match only messages received
   on the interface it uses (interface to ideal functionality). Messages
   from the adversary will flow through the simulator.

   The message paths of the matched messages must be fully qualified,
   and only output messages from the adversarial interface of the
   ideal functionality, or incoming adversarial messages to one of the
   components of the simulator real functionality can be matched (and
   the latter only in non-initial states).

   Unlike the functionality, the simulator's message match doesn't
   have to cover all of the possible messages, but it still cannot
   match a mesage that was covered by a previous match. *)

sim_def : 
  | SIM; name = id_l; USES uses = id_l;
    SIMS sims = id_l; args = option(fun_args);
    sms = state_machine_sim
      { let args =
          match args with
          | None      -> []
          | Some args -> args in
        {id = name; uses = uses; sims = sims; sims_arg_ids = args;
         states = sms } }

fun_args : 
  | LPAREN; args = separated_list(COMMA, id_l); RPAREN
      { args }

state_machine_sim : 
  | LBRACE; sds = list(state_def_sim) RBRACE
      { sds }

state_def_sim : 
  | INITIAL; st = state_sim
      { let l = loc((st : state).id) in
        let params = st.params in
        if not (List.is_empty params)
        then parse_error l "an initial state may not have parameters"
        else InitialState {id = st.id; params = []; code = st.code} }
  | st = state_sim
      { FollowingState
        {id = (st : state).id; params = st.params; code = st.code} }

state_sim : 
  | STATE; id = id_l; params = option(state_params); code = state_code_sim
      { let params = params |? [] in
        {id = id; params = params; code = code} : state }

state_code_sim : 
  | LBRACE; vars = local_var_decls; mm = message_matching_sim; RBRACE
      { {vars = vars; mmclauses = mm} }

message_matching_sim : 
  | MATCH; MESSAGE; WITH; PIPE?
    mmcs = separated_list(PIPE, msg_match_clause_sim); END
      { mmcs }

msg_match_clause_sim : 
  | msg_pat = msg_pat_sim; ARROW; code = inst_block
      { {msg_pat = msg_pat; code = code } }

(* no source port binding: *)

msg_pat_sim : 
  | msg = msg_path; pat_args = option(pat_args)
      { {port_id = None; path = msg; pat_args = pat_args} }

(* Instructions *)

inst_block : 
  | LBRACE; is = loc(list(instruction)); RBRACE
      { is }

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
  | i = control_transfer
      { i }

(* There are two instructions for assigning a value to the variable:
   ordinary assignment and random asssignment (from a distribution
   type). *)

assignment : 
  | vid = id_l; ASGVAL; e = expression; SEMICOLON
      { Assign (vid, e) }
  | vid = id_l; ASGSAMPLE; e = expression; SEMICOLON
      { Sample (vid, e) }

(* Conditional (if-then-else) instructions *)

ifthenelse : 
  | IF LPAREN; c = expression; RPAREN; tins = inst_block; ift = iftail
      { ITE (c, tins, ift) }

iftail : 
  | /* empty */
      { None }
  | ELSE; eins = inst_block
      { Some eins }
  | elif = elifthenelse
      { let l = loc elif in
        Some (mk_loc l [elif]) }

%inline elifthenelse :
  | x = loc(elifthenelse_u)
      { x }

elifthenelse_u : 
  | ELIF LPAREN; c = expression; RPAREN; tins = inst_block; ift = iftail
      { ITE (c, tins, ift) }

(* A decode command attempts to decode a value of type univ as some
   other type. If this succeeds, the variables in the pattern are
   bound. Otherwise the error branch is executed. *)

decode : 
  | DECODE; ex = expression; AS; ty = ty; WITH;
    PIPE? OK; args_pat = dec_pat; ARROW; code1 = inst_block;
    PIPE; ERROR; ARROW; code2 = inst_block; END;
      { Decode (ex, ty, args_pat, code1, code2) }

dec_pat : 
  | pat_args = pat_args
      { pat_args }
  | pat = pat
      { [pat] }

(* Control transfer instructions *)

control_transfer : 
  | sat = send_and_transition; DOT
      { SendAndTransition sat }
  | FAIL; DOT
      { Fail }

(* The send_and_transition command consists of two parts, the send
   part which sends a message, and the transition part designates the
   state to which control should later return to the functionality or
   simulator. Direct messages must have a destination port specified;
   adversarial and internal messages cannot have a port specified. In
   a functionality, the message paths for direct and adversarial
   messages do not need to be fully qualified when there is no
   ambiguity. But message paths for simulators do need to be fully
   qualified. *)

send_and_transition : 
  | SEND; msg = msg_expr; ANDTXT; TRANSITION; state = state_expr
      { {msg_expr = msg; state_expr = state} }

msg_expr : 
  | path = msg_path; args = option(args); port_id = option(dest)
      { let args = args |? [] in
        {path = path; args = args; port_id = port_id} }

dest :
  | AT; pv = id_l
      { pv }

state_expr : 
  | id = id_l; args = option(args)
      { let args = args |? [] in
        {id = id; args = args} }

(* Types *)

(* The typ type is a simplified version of ty type from EcTypes, for
   more info on what was removed from ec_types look at documentation
   in UcTypes. *)

type_binding : 
  | name = id_l; COLON; t = ty; { {id = name; ty = t} : type_binding }

type_bindings : 
  | ps = separated_list(COMMA, type_binding) { ps }

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

args :
  LPAREN; args = separated_list(COMMA, expression); RPAREN
    { args }

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

%inline s_expression :
  | x = loc(s_expression_u)
      { x }

s_expression_u : 
  | qid = qid
      { Id qid }
  | LPAREN; es = separated_list(COMMA, expression); RPAREN
      { Tuple es }

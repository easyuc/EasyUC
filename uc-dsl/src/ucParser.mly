(* Menhir Specification for UC DSL Parser (UcParser module) *)

%{

open Batteries
open Format
open EcUtils
open EcLocation
open UcSpec
open UcMessage

(* auxiliary definitions for msg_path_pat and msg_path *)

type msg_path_pat_item =
  | MsgPathPatItemId   of id
  | MsgPathPatItemStar of EcLocation.t

let to_msg_or_star (mpi : msg_path_pat_item) : msg_or_star =
  match mpi with
  | MsgPathPatItemId id  -> MsgOrStarMsg id
  | MsgPathPatItemStar l -> MsgOrStarStar l

let to_id (mpi : msg_path_pat_item) : id =
  match mpi with
  | MsgPathPatItemId id  -> id
  | MsgPathPatItemStar l ->
      parse_error l
      (fun ppf -> fprintf ppf "@[*@ cannot@ be@ followed@ by@ \".\"@]")

let rec to_msg_path_pat (mppis : msg_path_pat_item list) (mp : msg_path_pat) =
  match mppis with
  | []       -> failure "should never be empty"
  | [x]      ->
      {inter_id_path = mp.inter_id_path;
       msg_or_star   = to_msg_or_star x}
  | hd :: tl ->
      to_msg_path_pat tl
      {inter_id_path = mp.inter_id_path @ [to_id hd];
       msg_or_star   = mp.msg_or_star}

let msg_path_pat_items_to_msg_path_pat
    (mppis : msg_path_pat_item list) : msg_path_pat =
  to_msg_path_pat mppis
  {inter_id_path = []; msg_or_star = MsgOrStarStar _dummy}

let qid_to_msg_path (ids : qid) : msg_path =
  let iid = List.take (List.length ids - 1) ids in
  let msg = List.last ids in 
  {inter_id_path = iid; msg = msg}

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
        (fun ppf ->
           fprintf ppf
           "@[%s@ messages@ of@ direct@ interfaces@ must@ have@ %s@ ports@]"
           (if is_in then "input" else "output")
           (if is_in then "source" else "destination"))
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
        parse_error (loc id)
        (fun ppf ->
           fprintf ppf
           ("@[%s@ messages@ of@ adversarial@ interfaces@ cannot@ " ^^
            "have@ %s@ ports@]")
           (if is_in then "input" else "output")
           (if is_in then "source" else "destination")) in
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
%left     HAT
%right    ROP4

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

%inline id : 
  | id = loc(ID)
      { id }

%inline qid : 
  | qid = separated_nonempty_list(DOT, id)
      { qid }

(* a UC DSL specification consists of a preamble which references
  other .ec and .uc files, and a list of definitions of direct and
  adversarial interfaces, functionalities and simlators. *)

spec : 
  | ext = preamble; defs = list(def); EOF
      { {externals = ext; definitions = defs} }
        
preamble : 
  | uc_reqs = option(uc_requires); ec_reqs = option(ec_requires)
      { {uc_requires = uc_reqs |? [];
         ec_requires = ec_reqs |? []} }

(* require .uc files *)

uc_requires : 
  | UC_REQUIRES uc_reqs = nonempty_list(id) DOT
      { uc_reqs }

(* require import .ec files, making types and operators available
   for use in UC DSL specification *)

ec_requires : 
  | EC_REQUIRES ec_reqs = nonempty_list(id) DOT
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
   a nonempty sequence of named sub-interfaces, which are defined to be
   basic interfaces. Messages have typed parameters; when the list of
   parameters is empty, the "()" may be omitted.  In direct
   interfaces, input messages must have source ports (but may not have
   destination ports), whereas output messages must have destination
   ports (but may not have source ports). In adversarial interfaces,
   neither input nor output messages may have source or target
   ports. The names of message parameters as well as the names of
   source and destination ports should be considered documentation *)

inter_def : 
  | DIRECT; ni = named_inter
      { check_parsing_direct_inter ni;
        DirectInter ni }
  | ADVERSARIAL; ni = named_inter
      { check_parsing_adversarial_inter ni;
        AdversarialInter ni }

named_inter : 
  | inter_id = id; LBRACE; inter = loc(option(inter)); RBRACE
      { match unloc inter with
        | None       ->
            parse_error (loc inter)
            (fun ppf -> fprintf ppf "@[interfaces@ may@ not@ be@ empty@]")
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
  | IN; pt = id; AT; mb = message_body
      { {dir = In; id = (mb : message_body).id; params = mb.params;
         port = Some pt} }
  | OUT; mb = message_body
      { {dir = Out; id = (mb : message_body).id; params = mb.params;
         port = None} }
  | OUT; mb = message_body; AT; pt = id
      { {dir = Out; id = (mb : message_body).id; params = mb.params;
         port = Some pt} }

message_body :
  | msg_id = id; params = option(message_params)
      { let params = params |? [] in
        {id = msg_id; params = params} : message_body }

message_params :
  LPAREN; params = type_bindings; RPAREN
    { params }

comp_item :
  | sub_id = id; COLON; inter_id = id
      { {sub_id = sub_id; inter_id = inter_id} }

(* Functionalities *)

(* A functionality has a name, parameter list, an implementation
   specification, and a body.

   Parameters are functionalities that implement the specified
   composite direct interfaces. Parameter lists may be empty, in which
   case the "()" may be omitted. A real functionality may have a
   non-zero number of parameters, but an ideal functionality must have
   no parameters. Functionality parameters must be distinct from the
   names of top-level functionality interfaces.

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
   parameters, as well as distinct from the names of top-level
   interfaces, and which represent instances of ideal functionalities;
   followed by a nonempty list of party definitions.

   The body of an ideal functionality is a state machine. *)

fun_def :        
  | FUNCT; name = id; params = loc(option(fun_params));
    IMPLEM; dir_id = id; adv_id = option(id);
    fun_body = fun_body
      { let uparams = unloc params |? [] in
        let () =
          if not (is_real_fun_body fun_body) && not (List.is_empty uparams)
          then parse_error (loc params)
               (fun ppf ->
                  fprintf ppf
                  "@[ideal@ functionalities@ may@ not@ have@ parameters@]")
          else () in
        {id = name; params = uparams;
         id_dir = dir_id; id_adv = adv_id;
         fun_body = fun_body} }

fun_params : 
  | LPAREN; fps = separated_list(COMMA, fun_param); RPAREN
      { fps }

fun_param : 
  | name = id; COLON; id_dir = id
      { {id = name; id_dir = id_dir} : fun_param }

fun_body :
  | rfb = real_fun_body
      { FunBodyReal rfb }
  | ifb = ideal_fun_body
      { FunBodyIdeal ifb }

real_fun_body : 
  | LBRACE; sfs = list(sub_fun_decl); pdfs = loc(list(party_def)); RBRACE
      { if List.is_empty (unloc pdfs)
        then parse_error (loc pdfs)
             (fun ppf ->
                fprintf ppf
                "@[there@ must@ be@ at@ least@ one@ party@ definition@]");
        {sub_fun_decls = sfs; party_defs = unloc pdfs} : fun_body_real }

ideal_fun_body :
  | sm = state_machine
      { sm }

(* a subfunctionality declaration declares a new instance
   of an ideal functionality *)

sub_fun_decl : 
  | SUBFUN; id = id; EQ; fun_id = id;
      { {id = id; fun_id = fun_id} : sub_fun_decl }

(* A functionality party serves exactly one basic direct interface,
   which must be a sub-interface of the composite direct interface
   implemented by the functionality; the party serves at most one
   basic adversarial direct interface, which must be a sub-interface
   of the composite adversarial interface implemented by the
   functionality. Different parties can't serve the same basic
   interfaces, and the union of the basic interfaces served by the
   parties must sum up to the composite interfaces implemented by the
   functionality. The actions of a party are determined by a state
   machine.

   Basic direct interfaces are named by interface identifer paths, or
   inter id paths, consisting of the name of a composite interface,
   followed by the name of one of its sub-interfaces. *)

party_def : 
  | PARTY; id = id; serves = serves; sm = state_machine
     { {id = id; serves = serves; states = sm} }

serves : 
  | SERVES; serves = list(qid)
      { serves }

state_machine : 
  | LBRACE; sds = nonempty_list(state_def) RBRACE
      { sds }

(* A state machine consists of a list of named states, which are
   parameterized by typed values. The states must have unique names,
   and there must be exactly one initial state. That initial state
   must take no parameters. A state's code declares local variables,
   and describes how incoming messages should be matched and processed
   via a nonempty list of message matching clauses *)

state_def : 
  | INITIAL; st = state
      { let params = unloc st.params in
        if not (List.is_empty params)
        then parse_error (loc st.params)
             (fun ppf ->
                fprintf ppf
                "@[an@ initial@ state@ may@ not@ have@ parameters@]")
        else InitialState {id = st.id; params = st.params; code = st.code} }
  | st = state
      { FollowingState
        {id = (st : state).id; params = st.params; code = st.code} }

state : 
  | STATE; id = id; params = loc(option(state_params)); code = state_code
      { let uparams = unloc params |? [] in
        {id = id;
         params = mk_loc (loc params) uparams;
         code = code} : state }

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
  | VAR; lvs = nonempty_list (id); COLON; t = ty SEMICOLON
      { List.map (fun lv -> {id = lv; ty = t}) lvs }

(* Message matching specifies how incoming messages of a functionality
   should be processed, resulting in a state transition or
   failure. (The situation is similar for simulators, but see below.)

   A message path is a "."-separated sequence of identifiers, taking
   us - in the simplest case, starting from a functionality's direct
   composite interface - from the name of a composite interface, to
   the name of one of its sub-interfaces, to the name of one of the
   messages of the sub-interface's basic interface.

   The part of a message path excluding the message name is called
   an interface identifer path - or inter id path.

   The situation is analogous for the composite adversarial interface
   of a real functionality (when it exists). In the case of the basic
   adversarial interface of an ideal functionality, the path takes us
   from the name of that basic interface to the name of one of the
   messages of that interface.

   In the case of a subfunctionality of a real functionality, the path
   takes us from the name of the subfunctionality, to one of the
   sub-interfaces of the direct composite interface implemented by the
   ideal functionality that subfunctionality is an instance of, to one
   of the messages of the basic direct interface of that sub-interface.

   In the case of the parameter of a real functionality, the path
   takes us from the name of the parameter, to one of the
   sub-interfaces of the the direct composite interface corresponding
   to the parameter, to one of the messages of the basic direct
   interface of that sub-interface.

   An incoming message path is one that terminates with an incoming
   message, wheres an outcoming message path is one that terminates
   with an outgoing message. This is from the point of view of
   the functionality, though, so that outgoing messages in the case
   of subfunctionalities and parameters are incoming messages from
   the functionality's point of view, and vice versa.

   For example, suppose the functionality implements FwDir (and, in
   the case of a real functionality, that the party serves fwDir):

     direct fwDir {
       in pt1@fw_req(pt2 : port, u : univ)
       out fw_rsp(pt1 : port, u : univ)@pt2
     }

     direct FwDir {D : fwDir}

   Then FwDir.D.fw_req is the only valid incoming message path. If
   there is a subfunctionality

     subfun Fw1 = Forw

   of a real functionality, where the ideal functionality Forw has
   FwDir as its direct interface, then

     Fw1.D.fw_req

   will be a valid incoming message path.

   Message path patterns look like message paths, except that they may
   end with "*" to match any completion of the given incoming message path.

   E.g.,

     FwDir.D.fw_req
     * - matches any incoming message path
     FwDir.* - matches any incoming message path beginning with FwDir
     FwDir.D.* - matches any incoming message path beginning with FwDir.D

   A message pattern is then an incoming message path pattern followed
   by an optional tuple of argument patterns, and optionally preceded
   by a source port identifier. E.g.,

     pt@FwDir.D.fw_req(pt' : port, u' : univ)

   will match a FwDir.D.fw_req message, and in the process pt will be
   bound to its source port, and pt' and u' will be bound to the
   message arguments.

   Source port identifiers are mandatory when matching incoming messages
   from direct composite interfaces implemented by the functionality,
   but must be omitted when matching incoming messages from an
   adversarial interface implemented by the functionality (if any), as
   well as when matching direct messages originating from the
   subfunctionalities of real functionalities.

   Finally, a message matching clause consists of a message pattern
   followed by the code to run on a matching message. *)

message_matching :
  | MATCH; MESSAGE; WITH; PIPE?
    mmcs = loc(separated_list(PIPE, msg_match_clause)); END
     { if List.is_empty (unloc mmcs)
       then parse_error (loc mmcs)
            (fun ppf ->
               fprintf ppf
               "@[at@ least@ one@ message@ matching@ clause@ is@ required@]");
       unloc mmcs }

msg_match_clause :
  | msg_pat = msg_pat; ARROW; code = inst_block
      { (match msg_pat.msg_path_pat.msg_or_star with
         | MsgOrStarMsg _ -> ()
         | MsgOrStarStar l ->
             if Option.is_some msg_pat.pat_args
             then parse_error l
                  (fun ppf ->
                     fprintf ppf
                     ("@[message@ pattern@ whose@ path@ ends@ in@ \"*\"@ " ^^
                      "may@ not@ have@ pattern@ arguments@]")));
        {msg_pat = msg_pat; code = code } }

msg_pat :
  | port_id = id; AT; mmb = msg_pat_body
      { match (mmb : msg_pat_body).msg_path_pat.msg_or_star with
        | MsgOrStarMsg _ ->
            {port_id = Some port_id; msg_path_pat = mmb.msg_path_pat;
             pat_args = mmb.pat_args}
        | MsgOrStarStar _ ->
            parse_error (loc port_id)
            (fun ppf ->
               fprintf ppf
               ("message@ pattern@ whose@ path@ ends@ " ^^
                "in@ \"*\"@ may@ not@ bind@ source@ port")) }
  | mmb = msg_pat_body
      { {port_id = None; msg_path_pat = (mmb : msg_pat_body).msg_path_pat;
         pat_args = mmb.pat_args} }

msg_pat_body : 
  | msg_path_pat = msg_path_pat; pat_args = option(pat_args)
      { {msg_path_pat = msg_path_pat; pat_args = pat_args} : msg_pat_body }

pat_args :
  | LPAREN; pa = separated_list(COMMA, pat); RPAREN
      { pa }

pat : 
  | id = id
      { PatId id }
  | l = loc(UNDERSCORE)
      { PatWildcard (loc l) }

msg_path_pat : 
  | mpis = separated_nonempty_list(DOT, msg_path_pat_item)
      { (* STAR, if it appears, must be at end *)
        msg_path_pat_items_to_msg_path_pat mpis }

msg_path_pat_item : 
  | id = id
      { MsgPathPatItemId id }
  | l = loc(STAR)
      { MsgPathPatItemStar (loc l) }

(* Simulators *)

(* A simulator uses a basic adversarial interface, to communicate with
   an ideal functionality. It simulates a real functionality, applied
   to ideal functionalities (in the case the real functionality is
   parameterized). The simulation consists of interacting with the
   adversary approximately as the real functionality would.

   A simulator's state machine is the same as an ordinary state
   machine, except that the source ports of incoming messages may not
   be bound in message patterns, since for simulators the sender is
   always known (it is either the adversary or the ideal
   functionality).

   The initial state of the simulator can match only messages received
   on the interface it uses (interface to ideal functionality). Messages
   from the adversary will flow through the simulator. (Before the initial
   message arrives from the ideal functionality, the simulator doesn't
   know the address of the ideal (and thus real) functionality.

   Message paths for simulators look like the following, where: USES
   is the basic adversarial interface the simulator uses to
   communicate with the ideal functionality; and SIMS is the real
   functionality the simulator simulates.

     USES.msg

       from the simulator's point of view: "in" messages are outgoing,
       and so can be pattern matched by the simulator; and "out"
       message are incoming ones, and so can be output by the
       simulator

     SIMS.RFAdv.BasicAdv.msg

       where RFAdv is the composite adversarial interface (if any)
       that SIMS implements

     SIMS.SubFun.BasicAdv.msg

       where SubFun is a subfunctionality of SIMS, BasicAdv is the
       basic adversarial interface of the ideal functionality that
       SubFun is an instance of, and msg is one of BasicAdv's messages

     SIMS.Param.BasicAdv.msg

       where Param is a parameter name of SIMS, BasicAdv is the basic
       adversarial interface the corresponding argument (an ideal
       functionality) implements, and msg is one of BasicAdv's
       messages

   Expressions in simulators may used qualified identifers of the form
   SIMS.Party, where Party is the name of one of SIMS's parties, which
   have type port and stand for the internal port of the given party
   *)

sim_def : 
  | SIM; name = id; USES uses = id;
    SIMS sims = id; args = loc(option(fun_args));
    sms = state_machine
      { let uargs = unloc args |? [] in
        {id = name; uses = uses; sims = sims;
         sims_arg_ids = mk_loc (loc args) uargs; states = sms} }

fun_args : 
  | LPAREN; args = separated_list(COMMA, id); RPAREN
      { args }

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
  | vid = id; ASGVAL; e = expression; SEMICOLON
      { Assign (vid, e) }
  | vid = id; ASGSAMPLE; e = expression; SEMICOLON
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
   other type. If this succeeds, the identifiers in the pattern are
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
   part which sends a message, and the transition part which
   designates the state to which control should later return to in the
   functionality or simulator. The send part consists of a message
   expression, whereas the transition part consists of a state
   expression.

   A message expression consists of an outgoing message path, followed
   by an optional list of arguments, of the types expected by the
   message.  Direct messages to sub-interfaces of the composite direct
   interface implemented by a real functionality must have destination
   ports specified. Direct messages to sub-functionalities of real
   functionalities must not have destination ports specified, and this
   is also true for all adversarial messages in functionalities and
   simulators.

   State expressions consist of a state name of the same state
   machine, followed by an optional list of arguments of the types
   expected by that state. *)

send_and_transition : 
  | SEND; msg = msg_expr; ANDTXT; TRANSITION; state = state_expr
      { {msg_expr = msg; state_expr = state} }

msg_path :
  | qid = qid
      { qid_to_msg_path qid }

msg_expr : 
  | path = msg_path; args = loc(option(args)); port_id = option(dest)
      { let uargs = unloc args |? [] in
        {path = path; args = mk_loc (loc args) uargs; port_id = port_id} }

dest :
  | AT; pv = id
      { pv }

state_expr : 
  | id = id; args = loc(option(args))
      { let uargs = unloc args |? [] in
        {id = id; args = mk_loc (loc args) uargs} }

(* Types *)

(* The typ type is a simplified version of ty type from EcTypes, for
   more info on what was removed from ec_types look at documentation
   in UcTypes.

   port and univ are special types, introduced by the DSL *)

type_binding : 
  | name = id; COLON; t = ty; { {id = name; ty = t} : type_binding }

type_bindings : 
  | ps = separated_list(COMMA, type_binding) { ps }

ty : 
  | name = id
      { NamedTy name }
  | tuphd = ty_br; STAR; tuptl = separated_nonempty_list(STAR, ty_br)
      { TupleTy (tuphd :: tuptl) }

ty_br : 
  | name = id
      { NamedTy name }
  | LPAREN; tuphd = ty_br; STAR;
    tuptl = separated_nonempty_list(STAR, ty_br); RPAREN
      { TupleTy (tuphd :: tuptl) }

(* Expressions *)

args :
  LPAREN; args = separated_list(COMMA, expression); RPAREN
    { args }

(* The syntax for expressions and operators is a simplified version of
   the syntax from EcParser of EasyCrypt.

   In real functionalities, the names of parties can be used as
   values of type port in expressions. They stand for the internal
   ports of those parties.

   In a simulator that simulates a real functionality SIMS, SIMS.Party,
   where Party is one of SIMS's parties, can be used in expressions
   with type port with the same meaning. *)

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
  | f = id; args = s_expression+
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

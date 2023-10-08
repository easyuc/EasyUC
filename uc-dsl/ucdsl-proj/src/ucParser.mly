(* Menhir Specification for UC DSL Parser (UcParser module) *)

(* indicated portions of this file are adapted from the EasyCrypt
   lexer, src/ucParser.mly *)

%{

open Batteries
open Format

open EcUtils
open EcLocation
open EcSymbols

open UcSpec
open UcSpecTypedSpecCommon
open UcMessage

module BI = EcBigInt

(* auxiliary functions for symbols and expressions *)

let pqsymb_of_psymb (x : psymbol) : pqsymbol =
  mk_loc x.pl_loc ([], x.pl_desc)

let pqsymb_of_symb loc (x : symbol) : pqsymbol =
  mk_loc loc ([], x)

let mk_peid_symb loc (s : symbol) (ti : ptyinstan option) : pexpr =
  mk_loc loc (PEident (pqsymb_of_symb loc s, ti))

let peapp_symb loc (s : symbol) (ti : ptyinstan option) (es : pexpr list) =
  PEapp (mk_peid_symb loc s ti, es)

let peget loc (ti : ptyinstan option) (e1 : pexpr) (e2 : pexpr) =
  peapp_symb loc EcCoreLib.s_get ti [e1; e2]

let peset loc (ti : ptyinstan option) (e1 : pexpr) (e2 : pexpr) (e3 : pexpr) =
  peapp_symb loc EcCoreLib.s_set ti [e1; e2; e3]

let pe_nil loc (ti : ptyinstan option) =
  mk_peid_symb loc EcCoreLib.s_nil ti

let pe_cons loc (ti : ptyinstan option) (e1 : pexpr) (e2 : pexpr) =
  mk_loc loc (peapp_symb loc EcCoreLib.s_cons ti [e1; e2])

let pelist loc (ti : ptyinstan option) (es : pexpr list) : pexpr =
  List.fold_right (fun e1 e2 -> pe_cons loc ti e1 e2) es (pe_nil loc ti)

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
        error_message
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
        error_message (loc id)
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

  (* ------------------------------------------------------------------ *)
  type prover =
    [ `Exclude | `Include | `Only] * psymbol

  type pi = [
    | `DBHINT of EcParsetree.pdbhint
    | `INT    of int
    | `PROVER of prover list
  ]

  type smt = [
    | `ALL
    | `ITERATE
    | `QUORUM         of int
    | `MAXLEMMAS      of int option
    | `MAXPROVERS     of int
    | `PROVER         of prover list
    | `TIMEOUT        of int
    | `UNWANTEDLEMMAS of EcParsetree.pdbhint
    | `WANTEDLEMMAS   of EcParsetree.pdbhint
    | `VERBOSE        of int option
    | `VERSION        of [ `Full | `Lazy ]
    | `DUMPIN         of string located
    | `SELECTED
    | `DEBUG
  ]

  module SMT : sig
    val mk_pi_option  : psymbol -> pi option -> smt
    val mk_smt_option : smt list -> EcParsetree.pprover_infos
  end = struct
    open EcParsetree
    let option_matching tomatch =
      let match_option = String.option_matching tomatch in
      fun s ->
        match match_option s.pl_desc with
        | [m] -> mk_loc s.pl_loc m
        | []  ->
            error_message s.pl_loc
            (fun ppf ->
               Format.fprintf ppf "unknown option: %s" (unloc s))
        | ls  ->
            error_message s.pl_loc
            (fun ppf ->
               Format.fprintf ppf
               "option `%s` is ambiguous; matching ones are: `%s`"
               (unloc s) (String.concat ", " ls))

    let option_matching =
       option_matching
         [ "all"            ;
           "quorum"         ;
           "timeout"        ;
           "maxprovers"     ;
           "maxlemmas"      ;
           "wantedlemmas"   ;
           "unwantedlemmas" ;
           "prover"         ;
           "verbose"        ;
           "lazy"           ;
           "full"           ;
           "iterate"        ;
           "dumpin"         ;
           "selected"       ;
           "debug"          ]

    let as_int = function
      | None          -> `None
      | Some (`INT n) -> `Some n
      | Some _        -> `Error

    let as_dbhint = function
      | None             -> `None
      | Some (`DBHINT d) -> `Some d
      | Some _           -> `Error

    let as_prover = function
      | None             -> `None
      | Some (`PROVER p) -> `Some p
      | Some _           -> `Error

    let get_error ~optional s name =
      error_message s.pl_loc
      (fun ppf ->
         Format.fprintf ppf
          "`%s`: %s`%s` option expected" (unloc s)
          (if optional then "optional " else "")
          name)

    let get_as (name, getter) s o =
      match getter o with
      | `Some v -> v
      | `None
      | `Error  -> get_error ~optional:false s name

    let get_opt_as (name, getter) s o =
      match getter o with
      | `Some v -> Some v
      | `None   -> None
      | `Error  -> get_error ~optional:true s name

    let get_as_none s o =
      if EcUtils.is_some o then
          error_message s.pl_loc
          (fun ppf ->
             Format.fprintf ppf
             "`%s`: no option expected" (unloc s))

    let mk_pi_option (s : psymbol) (o : pi option) : smt =
      let s = option_matching s in

      match unloc s with
      | "timeout"        -> `TIMEOUT        (get_as     ("int"   , as_int) s o)
      | "quorum"         -> `QUORUM         (get_as     ("int"   , as_int) s o)
      | "maxprovers"     -> `MAXPROVERS     (get_as     ("int"   , as_int) s o)
      | "maxlemmas"      -> `MAXLEMMAS      (get_opt_as ("int"   , as_int) s o)
      | "wantedlemmas"   ->
          `WANTEDLEMMAS   (get_as ("dbhint", as_dbhint) s o)
      | "unwantedlemmas" ->
          `UNWANTEDLEMMAS (get_as ("dbhint", as_dbhint) s o)
      | "prover"         ->
          `PROVER         (get_as ("prover", as_prover) s o)
      | "verbose"        -> `VERBOSE        (get_opt_as ("int"   , as_int) s o)
      | "lazy"           -> `VERSION        (get_as_none s o; `Lazy)
      | "full"           -> `VERSION        (get_as_none s o; `Full)
      | "all"            -> get_as_none s o; (`ALL)
      | "iterate"        -> get_as_none s o; (`ITERATE)
      | "selected"       -> get_as_none s o; (`SELECTED)
      | "debug"          -> get_as_none s o; (`DEBUG)
      | _                ->  assert false

    let mk_smt_option (os : smt list) =
      let mprovers = ref None in
      let timeout  = ref None in
      let pnames   = ref None in
      let quorum   = ref None in
      let all      = ref None in
      let mlemmas  = ref None in
      let wanted   = ref None in
      let unwanted = ref None in
      let verbose  = ref None in
      let version  = ref None in
      let iterate  = ref None in
      let dumpin   = ref None in
      let selected = ref None in
      let debug    = ref None in

      let is_universal p = unloc p = "" || unloc p = "!" in

      let ok_use_only pp p =
        if pp.pp_add_rm <> [] then
          error_message (loc p)
          (fun ppf ->
             Format.fprintf ppf
             "use-only elements must come at beginning")
        else if pp.pp_use_only <> [] && is_universal p then
          error_message (loc p)
          (fun ppf ->
             Format.fprintf ppf
             "cannot add universal to non-empty use-only")
        else
          match pp.pp_use_only with
          | [q] ->
              if is_universal q then
                error_message (loc p)
                (fun ppf ->
                   Format.fprintf ppf
                   "use-only part is already universal")
          | _ -> () in

      let add_prover (k, p) =
        let r  = odfl empty_pprover_list !pnames in
        let pr =
          match k with
          | `Only ->
	            ok_use_only r p; { r with pp_use_only = p :: r.pp_use_only }
          | `Include -> { r with pp_add_rm = (`Include, p) :: r.pp_add_rm }
          | `Exclude -> { r with pp_add_rm = (`Exclude, p) :: r.pp_add_rm }

        in pnames := Some pr in

      let do1 o  =
        match o with
        | `ALL              -> all      := Some true
        | `QUORUM         n -> quorum   := Some n
        | `TIMEOUT        n -> timeout  := Some n
        | `MAXPROVERS     n -> mprovers := Some n
        | `MAXLEMMAS      n -> mlemmas  := Some n
        | `WANTEDLEMMAS   d -> wanted   := Some d
        | `UNWANTEDLEMMAS d -> unwanted := Some d
        | `VERBOSE        v -> verbose  := Some v
        | `VERSION        v -> version  := Some v
        | `ITERATE          -> iterate  := Some true
        | `PROVER         p -> List.iter add_prover p
        | `DUMPIN         f -> dumpin   := Some f
        | `SELECTED         -> selected := Some true
        | `DEBUG            -> debug    := Some true
      in

      List.iter do1 os;

      oiter
        (fun r -> pnames := Some { r with pp_add_rm = List.rev r.pp_add_rm })
        !pnames;

      { pprov_max       = !mprovers;
        pprov_timeout   = !timeout;
        pprov_cpufactor =  None;
        pprov_names     = !pnames;
        pprov_quorum    = !quorum;
        pprov_verbose   = !verbose;
        pprov_version   = !version;
        plem_all        = !all;
        plem_max        = !mlemmas;
        plem_iterate    = !iterate;
        plem_wanted     = !wanted;
        plem_unwanted   = !unwanted;
        plem_dumpin     = !dumpin;
        plem_selected   = !selected;
        psmt_debug      = !debug;
      }
  end

%}
%token <Lexing.position> FINAL (* a "." followed by whitespace of eof *)
%token EOF  (* end-of-file *)

%token <EcSymbols.symbol> LIDENT  (* lower identifier *)
%token <EcSymbols.symbol> UIDENT  (* upper identifier *)
%token <EcSymbols.symbol> TIDENT  (* type identifier (variable) *)
%token <EcSymbols.symbol> PUNIOP  (* parenthesized unary operator *)
%token <EcSymbols.symbol> PBINOP  (* parenthesized binary operator *)
%token <EcSymbols.symbol> PNUMOP  (* parenthesized numeric operator *)
%token <EcBigInt.zint> UINT       (* unsigned integer constant *)
%token <EcBigInt.zint * (int * EcBigInt.zint)> DECIMAL  (* decimal constant *)
%token <string> STRING  (* string *)

(* keywords *)

%token ADVERSARIAL
%token ANDTXT
%token DIRECT
%token EC_REQUIRES
%token ELIF
%token ELSE
%token END
%token ENVPORT
%token EXIST
%token FAIL
%token FORALL
%token FUN
%token FUNCT
%token IF
%token IMPLEM
%token IN
%token INITIAL
%token INTPORT
%token LET
%token MATCH
%token MESSAGE
%token OUT
%token PARTY
%token PROVER
%token SEND
%token SERVES
%token SIM
%token SIMS
%token STATE
%token SUBFUN
%token THEN
%token TIMEOUT
%token TOP
%token TRANSITION
%token UC_REQUIRES
%token USES
%token VAR
%token WITH
%token ASSERT
%token ASSUMPTION
%token UNDO
%token DEBUG

(* fixed length *)

%token AT
%token COLON
%token COLONTILD
%token COMMA
%token DLBRACKET
%token DOLLAR
%token DOT
%token DOTDOT
%token DOTTICK
%token LARROW
%token LBRACE
%token LBRACKET
%token LESAMPLE
%token LPAREN
%token LPBRACE
%token LTCOLON
%token PCENT
%token PIPE
%token QUESTION
%token RBOOL
%token RBRACE
%token RBRACKET
%token RPAREN
%token RPBRACE
%token SEMICOLON
%token TICKPIPE
%token TILD
%token UNDERSCORE

(* type and expression operators, some used for other purposes too *)

%token <string> NOP LOP1 ROP1 LOP2 ROP2 LOP3 ROP3 LOP4 ROP4 NUMOP
%token IMPL   (* other uses *)
%token SLASH
%token NOT
%token AMP
%token HAT
%token ANDA
%token AND
%token ORA
%token OR
%token IFF
%token PLUS
%token MINUS
%token STAR   (* other uses *) 
%token EQ     (* other uses *)
%token NE
%token GT
%token LT
%token GE
%token LE
%token RARROW

(* precedence and associativity *)

%nonassoc COMMA ELSE

%nonassoc IN

%right    IMPL 
%nonassoc IFF
%right    ORA  OR
%right    ANDA AND
%nonassoc NOT

%nonassoc EQ NE

%nonassoc prec_below_order

%left     NOP
%left     GT LT GE LE
%left     LOP1
%right    ROP1
%right    QUESTION
%left     LOP2 MINUS PLUS
%right    ROP2
%right    RARROW
%left     LOP3 STAR SLASH
%right    ROP3
%left     LOP4 AT AMP HAT
%right    ROP4

(* the input for the UcParser is a list of tokens produced by UcLexer
   from the UC DSL file.  This list is parsed by UcParser, starting
   from one of the following start productions, producing a value
   of the corresponding type (defined in UcSpec). *)

%type <UcSpec.spec> spec
%type <UcSpec.fun_expr> fun_expr_start
%type <UcSpec.sent_msg_expr> sent_msg_expr_start
%type <UcSpec.pty> ty_start
%type <UcSpec.pexpr> expr_start
%type <UcSpec.interpreter_command> interpreter_command

(* in the generated ucParser.ml : 

val spec : (Lexing.lexbuf -> UcParser.token) -> Lexing.lexbuf -> UcSpec.spec

   and similarly for the other start symbols *)

%start spec fun_expr_start sent_msg_expr_start ty_start expr_start
       interpreter_command

%%
(*for testing purposes, to be removed*)
expr_start : x=expr EOF {x}
ty_start : x=loc(type_exp) EOF {x}
fun_expr_start : x=fun_expr EOF {x}
sent_msg_expr_start : x=sent_msg_expr EOF {x}

(* a UC DSL specification consists of a preamble which requires
  other .ec and .uc files, followed by a list of definitions of direct and
  adversarial interfaces, functionalities and simlators *)

spec : 
  | ext = preamble; defs = list(def); EOF
      { {externals = ext; definitions = defs} }
        
preamble : 
  | uc_reqs = option(uc_requires); ec_reqs = option(ec_requires)
      { {uc_requires = uc_reqs |? [];
         ec_requires = ec_reqs |? []} }

(* require .uc files *)

uc_requires : 
  | UC_REQUIRES; uc_reqs = nonempty_list(ident); final_or_dot
      { uc_reqs }

final_or_dot :
  | FINAL { }  (* a "." followed by whitespace or end-of_file *)
  | DOT   { }  (* a "." not so followed *)

(* require .ec files, making types and operators available for use in
   UC DSL specification

   +id means also do an import, id means no import *)

ec_requires : 
  | EC_REQUIRES; ec_reqs = nonempty_list(require); final_or_dot
      { ec_reqs }

require :
  | x = option(PLUS); id = ident
      { (id, Option.is_some x) }

(* A definition is either a definition of an interface, a
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
  | inter_id = uident; LBRACE; inter = loc(option(inter)); RBRACE
      { match unloc inter with
        | None       ->
            error_message (loc inter)
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
  | IN; pt = lident; AT; mb = message_body
      { {dir = In; id = (mb : message_body).id; params = mb.params;
         port = Some pt} }
  | OUT; mb = message_body
      { {dir = Out; id = (mb : message_body).id; params = mb.params;
         port = None} }
  | OUT; mb = message_body; AT; pt = lident
      { {dir = Out; id = (mb : message_body).id; params = mb.params;
         port = Some pt} }

message_body :
  | msg_id = lident; params = option(message_params)
      { let params = params |? [] in
        {id = msg_id; params = params} : message_body }

message_params :
  LPAREN; params = type_bindings; RPAREN
    { params }

comp_item :
  | sub_id = uident; COLON; inter_id = uident
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
  | FUNCT; name = uident; params = loc(option(fun_params));
    IMPLEM; dir_id = uident; adv_id = option(uident);
    fun_body = fun_body
      { let uparams = unloc params |? [] in
        let () =
          if not (is_real_fun_body fun_body) && not (List.is_empty uparams)
          then error_message (loc params)
               (fun ppf ->
                  fprintf ppf
                  "@[ideal@ functionalities@ may@ not@ have@ parameters@]")
          else () in
        {id = name; params = uparams;
         dir_id = dir_id; adv_id = adv_id;
         fun_body = fun_body} }

fun_params : 
  | LPAREN; fps = separated_list(COMMA, fun_param); RPAREN
      { fps }

fun_param : 
  | name = uident; COLON; dir_qid = uqident  (* qualified, allowing different
                                                root *)
      { {id = name; dir_qid = dir_qid} : fun_param }

fun_body :
  | rfb = real_fun_body
      { FunBodyReal rfb }
  | ifb = ideal_fun_body
      { FunBodyIdeal ifb }

real_fun_body : 
  | LBRACE; sfs = list(sub_fun_decl); pdfs = loc(list(party_def)); RBRACE
      { if List.is_empty (unloc pdfs)
        then error_message (loc pdfs)
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
  | SUBFUN; id = uident; EQ; fun_qid = uqident;  (* qualified, allowing
                                                    different root *)
      { {id = id; fun_qid = fun_qid} : sub_fun_decl }

(* A functionality party serves at most one basic direct interface,
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
  | PARTY; id = uident; serves = serves; sm = state_machine
     { {id = id; serves = serves; states = sm} }

serves : 
  | SERVES; serves = list(uqident)
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
      { let params = unloc (st : state).params in  (* type hint necessary *)
        if not (List.is_empty params)
        then error_message (loc st.params)
             (fun ppf ->
                fprintf ppf
                "@[an@ initial@ state@ may@ not@ have@ parameters@]")
        else InitialState {id = st.id; params = st.params; code = st.code} }
  | st = state
      { FollowingState
        {id = (st : state).id; params = st.params; code = st.code} }

state : 
  | STATE; id = uident; params = loc(option(state_params)); code = state_code
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
  | VAR; lvs = separated_nonempty_list(COMMA, lident); COLON;
    t = loc(type_exp) SEMICOLON
      { List.map (fun lv -> {id = lv; ty = t}) lvs }

(* Message matching specifies how incoming messages of an ideal
   functionality or a party of a real functionality should be
   processed in a given state, resulting in a state transition or
   failure. (The situation is similar for simulators, but see below.)

   A message path is a "."-separated sequence of identifiers, taking
   us - in the simplest case, starting from a functionality's direct
   composite interface - from the name of a composite interface
   (served by the party, in the case of a real functionality), to the
   name of one of its sub-interfaces, to the name of one of the
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
   sub-interfaces of the direct composite interface corresponding
   to the parameter, to one of the messages of the basic direct
   interface of that sub-interface.

   An incoming message path is one that terminates with an incoming
   message, wheres an outcoming message path is one that terminates
   with an outgoing message. This is from the point of view of
   the functionality, though, so that outgoing messages in the case
   of subfunctionalities and parameters are incoming messages from
   the functionality's point of view, and vice versa.

   For example, suppose the functionality implements FwDir (and, in
   the case of a real functionality, that the party serves fwDir.D):

     direct FwDir_ {
       in pt1@fw_req(pt2 : port, u : univ)
       out fw_rsp(pt1 : port, u : univ)@pt2
     }

     direct FwDir {D : FwDir_}

   Then FwDir.D.fw_req is the only valid incoming message path. If
   there is a subfunctionality

     subfun Fw1 = Forwarding.Forw

   of a real functionality, where the ideal functionality
   Fowarding.Forw has FwDir as its direct interface, then

     Fw1.D.fw_rsp

   will be a valid incoming message path.

   Message path patterns look like message paths, except that they may
   end with "*" to match any completion of the given incoming message
   path.

   E.g.,

     FwDir.D.fw_rsp
     * - matches any incoming message path
     FwDir.* - matches any incoming message path beginning with FwDir
     FwDir.D.* - matches any incoming message path beginning with FwDir.D

   A message pattern is then an incoming message path pattern followed
   by an optional tuple of argument patterns, and optionally preceded
   by a source port identifier. E.g.,

     pt@FwDir.D.fw_rsp(pt' : port, u' : univ)

   will match a FwDir.D.fw_rsp message, and in the process pt will be
   bound to its source port, and pt' and u' will be bound to the
   message arguments.

   Source port identifiers are mandatory when matching incoming messages
   from direct composite interfaces implemented by the functionality,
   but must be omitted when matching incoming messages from an
   adversarial interface implemented by the functionality (if any), as
   well as when matching direct messages originating from the
   subfunctionalities or parameters of real functionalities.

   A message matching clause consists of a message pattern followed by
   the code to run on a matching message. A message matching instruction
   consists of a sequence of clauses, which are applied in order.

   Adversarial messages cannot be matched in initial states of ideal
   functionalities or real functionality parties; they implicitly
   result in failure.

   At every state, there must be at least one incoming message path.
   The message matching clauses must be exhaustive - cover all
   possible paths - and non-redundant. *)


message_matching :
  | MATCH; MESSAGE; WITH; PIPE?
    mmcs = loc(separated_list(PIPE, msg_match_clause)); END
     { if List.is_empty (unloc mmcs)
       then error_message (loc mmcs)
            (fun ppf ->
               fprintf ppf
               "@[at@ least@ one@ message@ matching@ clause@ is@ required@]");
       unloc mmcs }

msg_match_clause :
  | msg_pat = msg_pat; IMPL; code = inst_block
      { (let mp = msg_pat.msg_path_pat in
         match (unloc mp).msg_or_star with
         | MsgOrStarMsg _ -> ()
         | MsgOrStarStar  ->
             if not (isUnconditionalFailure code)
               then error_message (loc code)
                    (fun ppf ->
                       fprintf ppf
                       ("@[message@ match@ clause@ whose@ message@ " ^^
                        "pattern@ has@ path@ ending@ in@ a@ \"*\"@ " ^^
                        "must@ have@ instruction@ block@ that@ is@ " ^^
                        "simply@ failure@]"))
             else if Option.is_some msg_pat.pat_args
               then error_message (loc mp)
                    (fun ppf ->
                       fprintf ppf
                       ("@[message@ pattern@ whose@ path@ ends@ in@ \"*\"@ " ^^
                        "may@ not@ have@ pattern@ arguments@]")));
        {msg_pat = msg_pat; code = code } }

msg_pat :
  | port_id = lident; AT; mmb = msg_pat_body
      { match (unloc
               ((mmb : symbol msg_pat_body).msg_path_pat)).msg_or_star with
        | MsgOrStarMsg _ ->
            {port_id = Some port_id; msg_path_pat = mmb.msg_path_pat;
             pat_args = mmb.pat_args}
        | MsgOrStarStar  ->
            error_message (loc port_id)
            (fun ppf ->
               fprintf ppf
               ("message@ pattern@ whose@ path@ ends@ " ^^
                "in@ \"*\"@ may@ not@ bind@ source@ port")) }
  | mmb = msg_pat_body
      { {port_id = None;
         msg_path_pat = (mmb : symbol msg_pat_body).msg_path_pat;
         pat_args = mmb.pat_args} }

msg_pat_body : 
  | msg_path_pat = msg_path_pat; pat_args = option(pat_args)
      { {msg_path_pat = msg_path_pat; pat_args = pat_args}
          : symbol msg_pat_body }

pat_args :
  | LPAREN; pa = separated_list(COMMA, pat); RPAREN
      { pa }

pat : 
  | id = lident
      { PatId id }
  | l = loc(UNDERSCORE)
      { PatWildcard (loc l) }

msg_path_pat : 
  | mppqid = genqident(msg_path_end)
      { let l = loc mppqid in
        let (iip, msg_or_star) = unloc mppqid in
        mk_loc l {inter_id_path = iip; msg_or_star = msg_or_star} }

msg_path_end : 
  | id = lident
      { MsgOrStarMsg (unloc id) }
  | STAR
      { MsgOrStarStar }

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
   know the address of the ideal (and thus real) functionality.) As
   with message matching in functionalities, it is an error if there
   are no incoming message paths in a given state.

   Message paths for simulators look like the following, where: USES
   is the basic adversarial interface the simulator uses to
   communicate with the ideal functionality; and SIMS is the real
   functionality the simulator simulates.

     USES.msg

       from the simulator's point of view: "out" messages are
       incoming, and so can be pattern matched by the simulator; and
       "in" message are outgoing ones, and so can be output by the
       simulator

     SIMS.RFAdv.SI.msg

       where RFAdv is the composite adversarial interface (if any)
       that SIMS implements, and SI is one of its sub-interfaces

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
  | SIM; name = uident; USES uses = uident;
    SIMS sims = uident; args = loc(option(sim_fun_args));
    sms = state_machine
      { let uargs = unloc args |? [] in
        {id = name; uses = uses; sims = sims;
         sims_arg_qids = mk_loc (loc args) uargs; states = sms} }

sim_fun_args : 
  | LPAREN; args = separated_list(COMMA, uqident); RPAREN
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
  | i = match_in
      { i }
  | i = control_transfer
      { i }

(* Assignments

   There are two instructions for assigning a value to the variable:
   ordinary assignment and random asssignment (from a distribution
   type). Both take a left-hand-side that is either a single variable
   or a tuple of variables with at least two elements. *)

assign_lhs :
  | id = lident
      { LHSSimp id }
  | LPAREN; ids = plist2(lident, COMMA); RPAREN
      { LHSTuple ids }

assignment : 
  | lhs = assign_lhs; LARROW; e = expr; SEMICOLON
      { Assign (lhs, e) }
  | lhs = assign_lhs; LESAMPLE; e = expr; SEMICOLON
      { Sample (lhs, e) }

(* Conditional (if-then-else) Instructions *)

ifthenelse : 
  | IF LPAREN; c = expr; RPAREN; tins = inst_block; ift = iftail
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
  | ELIF LPAREN; c = expr; RPAREN; tins = inst_block; ift = iftail
      { ITE (c, tins, ift) }

(* Match Instructions *)

match_in :
  | MATCH; e = expr; WITH;
    PIPE?;
    lcs = loc
          (plist0
           (pat = mcptn(sbinop); IMPL; ins = inst_block { (pat, ins) },
            PIPE));
    END
      { if List.is_empty (unloc lcs)
        then error_message (loc lcs)
             (fun ppf ->
                Format.fprintf ppf
                "@[at@ least@ one@ matching@ clause@ is@ required@]");
        Match (e, lcs) }

(* Control Transfer Instructions *)

control_transfer : 
  | sat = send_and_transition; final_or_dot
      { SendAndTransition sat }
  | FAIL; final_or_dot
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
   expected by that state.

   Transitions back to initial states (of ideal functionalities,
   parties or real functionalities, or simulators) are not allowed -
   even originating from the initial state. A send-and-transition in
   the initial state of an ideal functionality must send an
   adversarial message (waking up its simulator, when there is one). *)

send_and_transition : 
  | SEND; msg = msg_expr; ANDTXT; TRANSITION; state = state_expr
      { {msg_expr = msg; state_expr = state} }

msg_path :
  | lqid = lqident
      { let l   = loc lqid in
        let qid = unloc lqid in
        mk_loc l {inter_id_path = fst qid; msg = snd qid} }

msg_expr : 
  | path = msg_path; args = loc(option(args)); port_expr = option(dest)
      { let uargs = unloc args |? [] in
        {path = path; args = mk_loc (loc args) uargs; port_expr = port_expr} }

dest :
  | AT; ex = idexpr
      { ex }
  | AT; LPAREN; ex = expr; RPAREN;
      { ex }

state_expr : 
  | id = uident; args = loc(option(args))
      { let uargs = unloc args |? [] in
        {id = id; args = mk_loc (loc args) uargs} }

(* Interpreter commands *)  

interpreter_command :
  | c = loc(icomm); FINAL;
      { c }
  | l=loc(EOF);
      { mk_loc (loc l) Quit }

icomm :
  | c = load_uc_file;     { c }
  | c = fun_ex_cmd;       { c }
  | c = comm_word;        { c }
  | c = send_msg;         { c }
  | c = prover_cmd;       { c }
  | c = undo_cmd;         { c }
  | c = add_var_cmd;      { c }
  | c = add_ass_cmd;      { c }
  | c = assert_cmd;       { c }
  | c = step_prover_info; { c }
  | c = debug_cmd         { c }

load_uc_file :
  | load = lident; file = ident; 
      {
        if (unloc load) = "load" 
        then Load file
        else error_message (loc load)
              (fun ppf ->
                 fprintf ppf
                 "@[did@ you@ mean@ load@ instead@ of@ %s?@]" (unloc load))
      }

undo_cmd :
  | UNDO; no = loc(word); { Undo no }

add_var_cmd :
  | VAR; v = type_binding; 
      { AddVar v }

add_ass_cmd :
  | ASSUMPTION; id = ident; COLON; f = expr;  
      { AddAss (id, f) }

fun_ex_cmd :
  | FUNCT; fe = fun_expr { FunEx fe }

comm_word :
  | cw = lident; 
      {
        match (unloc cw) with
        | "real"   -> World Real
        | "ideal"  -> World Ideal
        | "run"    -> Run
        | "step"   -> Step None
        | "finish" -> Finish
        | "quit"   -> Quit
        | _        -> 
          error_message (loc cw)
          (fun ppf -> fprintf ppf
             "@[%s@ is@ not@ a@ valid@ interpreter@ command@]" (unloc cw))
      }

assert_cmd :
  | c = assert_msg_out;      { c }
  | c = assert_other_effect; { c }

assert_msg_out:
  | ASSERT; w = lident; sme = sent_msg_expr; ct = assert_ctrl;
      {
        if (unloc w) = "msg_out" 
        then Assert (mk_loc (loc w) (EffectMsgOut (sme, ct)))
        else error_message (loc w)
              (fun ppf ->
                 fprintf ppf
                 "@[did@ you@ mean@ msg_out@ instead@ of@ %s?@]" (unloc w))
      }

assert_ctrl:
  | ct = lident;
      {
        match (unloc ct) with
        | "ctrl_env" -> CtrlEnv
        | "ctrl_adv" -> CtrlAdv
        | _          ->
           error_message (loc ct)
           (fun ppf ->
              fprintf ppf
              "@[did@ you@ mean@ ctrl_env@ or@ ctrl_adv@ instead@ of@ %s?@]" 
              (unloc ct))
      }

assert_other_effect :
  | ASSERT; ew = lident;
      {
        match (unloc ew) with
        | "ok"       -> Assert (mk_loc (loc ew) EffectOK)
        | "rand"     -> Assert (mk_loc (loc ew) EffectRand)
        | "fail_out" -> Assert (mk_loc (loc ew) EffectFailOut)
        | _          -> 
          error_message (loc ew)
          (fun ppf ->
             fprintf ppf "@[%s@ is@ not@ a@ valid@ effect@]" (unloc ew))
      }

send_msg :
  | SEND; sme = sent_msg_expr; { Send sme }

debug_cmd :
  | DEBUG ; { Debug }

step_prover_info :
  | step = lident; PROVER; pi = smt_info; 
    {
      if (unloc step) = "step" 
      then Step (Some pi)
      else error_message (loc step)
            (fun ppf ->
               fprintf ppf
               "@[did@ you@ mean@ step@ instead@ of@ %s?@]" (unloc step))
    }

prover_cmd:
  | PROVER x = smt_info { Prover x } 

fun_expr :
  | x = uqident; { FunExprNoArgs x }
  | x = uqident; LPAREN; y = separated_list(COMMA, fun_expr); RPAREN;
      { FunExprArgs (x,y) }

sent_msg_expr :
  | src_pex = poa_pexpr; 
    src_doa = dollar_or_at; 
    path = msg_path; 
    argsl = loc(option(args));
    dest_doa = dollar_or_at; 
    dest_pex = poa_pexpr; 
      { let uargsl = mk_loc (loc argsl) (unloc argsl |? []) in
        SME_Ord
        { src_poa_pexpr =
            if src_doa then PoA_Addr src_pex else PoA_Port src_pex;
          path = path;
          args = uargsl;
          dest_poa_pexpr =
            if dest_doa then PoA_Addr dest_pex else PoA_Port dest_pex;
        }
      }
  | src_port = poa_pexpr;
    AT; UNDERSCORE; AT;
    dest_port = poa_pexpr;
      { SME_EnvAdv
        { src_port_pexpr  = src_port;
          dest_port_pexpr = dest_port;
        }
      }

poa_pexpr:
  | id = idexpr; { id }
  | LPAREN; ex = expr; RPAREN; { ex }
  
dollar_or_at :
  | DOLLAR { true  }
  | AT     { false }

(* prover command *)

dbmap1:
  | f = dbmap_flag? x = dbmap_target
      { { EcParsetree.pht_flag = odfl `Include f;
          EcParsetree.pht_kind = (fst x);
          EcParsetree.pht_name = (snd x); } }

%inline dbmap_flag:
  | PLUS  { `Include }
  | MINUS { `Exclude }

%inline dbmap_target:
  | AT x = uqident { (`Theory, x) }
  | x = qident     { (`Lemma , x) }

dbhint:
  | m = dbmap1           { [m] }
  | m = paren( dbmap1* ) {  m  }

smt_info:
  | li = smt_info1* { SMT.mk_smt_option li}

smt_info1:
  | t = word
      { `MAXLEMMAS (Some t) }

  | TIMEOUT EQ t = word
      { `TIMEOUT t }

  | p = prover_kind
      { `PROVER p }

  | PROVER EQ p = prover_kind
      { `PROVER p }

  | x = lident po = prefix(EQ, smt_option)?
      { SMT.mk_pi_option x po }

prover_kind1:
  | l = loc(STRING)       { `Only   , l }
  | PLUS  l = loc(STRING) { `Include, l }
  | MINUS l = loc(STRING) { `Exclude, l }

prover_kind:
  | LBRACKET lp = prover_kind1* RBRACKET { lp }

%inline smt_option:
  | n = word        { `INT n    }
  | d = dbhint      { `DBHINT d }
  | p = prover_kind { `PROVER p }

(* Type Bindings and Arguments *)

type_binding : 
  | name = lident; COLON; t = loc(type_exp)
      { {id = name; ty = t} : type_binding }

type_bindings : 
  | ps = separated_list(COMMA, type_binding) { ps }

args :
  LPAREN; args = separated_list(COMMA, expr); RPAREN
    { args }

(* Identifiers, Words and Operators

   everything below adapted from EasyCrypt parser *)

%inline _lident :
  | x = LIDENT { x }

%inline _uident :
  | x = UIDENT { x }

%inline _tident :
  | x = TIDENT { x }

%inline lident: x = loc(_lident) { x }
%inline uident: x = loc(_uident) { x }
%inline tident: x = loc(_tident) { x }

%inline _ident :
  | x = _lident { x }
  | x = _uident { x }

%inline ident :
  | x = loc(_ident) { x }

%inline uint : n = UINT { n }

%inline word :
  | n = loc(UINT) {
      try BI.to_int (unloc n) with
      | BI.Overflow ->
          error_message (loc n)
          (fun ppf -> Format.fprintf ppf "@[literal@ is@ too@ large@]") }

%inline namespace :
  | nm = rlist1(UIDENT, DOT)
      { nm }

  | TOP; nm = rlist0(prefix(DOT, UIDENT), empty)
      { EcCoreLib.i_top :: nm }

_genqident(X) :
  | x = X { ([], x) }
  | xs = namespace; DOT; x = X { (xs, x) }

genqident(X) :
  | x = loc(_genqident(X)) { x }

%inline  qident : x = genqident(_ident ) { x }
%inline uqident : x = genqident(_uident) { x }
%inline lqident : x = genqident(_lident) { x }

%inline _boident :
  | x = _lident { x }
  | x = _uident { x }
  | x = PUNIOP  { x }
  | x = PBINOP  { x }
  | x = PNUMOP  { x }

  | x = loc(STRING)   {
      if not (EcCoreLib.is_mixfix_op (unloc x)) then
        error_message x.pl_loc
        (fun ppf -> fprintf ppf "@[invalid@ mixfix@ operator@]");
    unloc x
  }

%inline _oident :
  | x = _boident      { x }
  | x = paren(PUNIOP) { x }

%inline boident: x = loc(_boident) { x }
%inline  oident: x = loc( _oident) { x }

qoident :
  | x = boident
      { pqsymb_of_psymb x }

  | xs = namespace; DOT; x = oident
  | xs = namespace; DOT; x = loc(NOP) {
    { pl_desc = (xs, unloc x);
      pl_loc  = EcLocation.make $startpos $endpos;
    }
  }

%inline ordering_op :
  | GT { ">"  }
  | LT { "<"  }
  | GE { ">=" }
  | LE { "<=" }

%inline uniop :
  | x = NOP { Printf.sprintf "[%s]" x }
  | NOT   { "[!]" }
  | PLUS  { "[+]" }
  | MINUS { "[-]" }

%inline sbinop :
  | EQ    { "="   }
  | PLUS  { "+"   }
  | MINUS { "-"   }
  | STAR  { "*"   }
  | SLASH { "/"   }
  | AT    { "@"   }
  | OR    { "\\/" }
  | ORA   { "||"  }
  | AND   { "/\\" }
  | ANDA  { "&&"  }
  | AMP   { "&"   }
  | HAT   { "^"   }

  | x = LOP1 | x = LOP2 | x = LOP3 | x = LOP4
  | x = ROP1 | x = ROP2 | x = ROP3 | x = ROP4
  | x = NOP
      { x }

%inline binop :
  | op = sbinop { op    }
  | IMPL        { "=>"  }
  | IFF         { "<=>" }

%inline numop :
  | op = NUMOP { op }

(* Patterns *)

bdident_ :
  | x = ident  { Some x }
  | UNDERSCORE { None }

%inline bdident :
  | x = loc(bdident_) { x }

lpattern_u :
  | x = ident
      { LPSymbol x }

  | LPAREN p = plist2(bdident, COMMA) RPAREN
      { LPTuple p }

  | LPBRACE fs = rlist1(lp_field, SEMICOLON) SEMICOLON? RPBRACE
      { LPRecord fs }

lp_field :
  | f = qident EQ x = ident { (f, x) }

%inline lpattern :
  | x = loc(lpattern_u) { x }

(* Types *)

simpl_type_exp :
  | x = qident                    { PTnamed x      }
  | x = tident                    { PTvar x        }
  | tya = type_args; x = qident   { PTapp (x, tya) }
  | LPAREN; ty = type_exp; RPAREN { ty             }

type_args :
  | ty = loc(simpl_type_exp)                          { [ty] }
  | LPAREN tys = plist2(loc(type_exp), COMMA) RPAREN  { tys  }

type_exp :
  | ty = simpl_type_exp                            { ty }
  | ty = plist2(loc(simpl_type_exp), STAR)         { PTtuple ty }
  | ty1 = loc(type_exp); RARROW; ty2=loc(type_exp) { PTfun(ty1, ty2) }

(* Expressions *)

tyvar_byname1:
| x = tident; EQ; ty = loc(type_exp) { (x, ty) }

tyvar_instan:
| lt = plist1(loc(type_exp), COMMA) { TVIunamed lt }
| lt = plist1(tyvar_byname1, COMMA) { TVInamed lt }

%inline tvars_instan:
| LTCOLON k = loc(tyvar_instan) GT { k }

%inline sexpr: x = loc(sexpr_u) { x }
%inline  expr: x = loc( expr_u) { x }

(* begin UC DSL *)

%inline idexpr: x = loc(idexpr_u) { x }

idexpr_u :
  | x = qoident; ti = tvars_instan?
      { PEident (x, ti) }

(* end UC DSL *)

sexpr_u :
  | e = sexpr; PCENT; p = uqident
      { PEscope (p, e) }

  | e=sexpr p=loc(prefix(PCENT, _lident))
      { if unloc p = "top" then
          PEscope (pqsymb_of_symb p.pl_loc "<top>", e)
        else
          let p = lmap (fun x -> "%" ^ x) p in
          PEapp (mk_loc (loc p) (PEident (pqsymb_of_psymb p, None)), [e]) }

  | LPAREN; e = expr; COLONTILD; ty = loc(type_exp); RPAREN
      { PEcast (e, ty) }

  | n = uint
      { PEint n }

  | d = DECIMAL
      { PEdecimal d }

(* begin UC DSL *)

  | x = loc(ENVPORT)  (* envport function *)
      { PEident (mk_loc (loc x) ([], "envport"), None) }

  | y = loc(INTPORT); x = uqident  (* internal port names *)
      { PEident
        (mk_loc (merge (loc y) (loc x))
         ([], "intport:" ^ string_of_qsymbol (unloc x)),
         None) }

  | x = idexpr_u; { x }

(* end UC DSL *)

  | op = loc(numop); ti = tvars_instan?
       { peapp_symb op.pl_loc op.pl_desc ti [] }

  | se = sexpr; DLBRACKET; ti = tvars_instan?; e = loc(plist1(expr, COMMA));
    RBRACKET
      { let e = List.reduce1 (fun _ -> lmap (fun x -> PEtuple x) e) (unloc e) in
        peget (EcLocation.make $startpos $endpos) ti se e }

  | se = sexpr; DLBRACKET; ti = tvars_instan?; e1=loc(plist1(expr, COMMA));
    LARROW e2=expr RBRACKET
      { let e1 =
          List.reduce1 (fun _ -> lmap (fun x -> PEtuple x) e1) (unloc e1) in
        peset (EcLocation.make $startpos $endpos) ti se e1 e2 }

  | TICKPIPE; ti = tvars_instan?; e = expr; PIPE
      { peapp_symb e.pl_loc EcCoreLib.s_abs ti [e] }

  | LBRACKET; ti = tvars_instan?; es = loc(plist0(expr, SEMICOLON)); RBRACKET
      { unloc (pelist es.pl_loc ti es.pl_desc) }

  | LBRACKET; ti = tvars_instan?; e1 = expr; op = loc(DOTDOT); e2=expr; RBRACKET
      { let id =
          PEident (mk_loc op.pl_loc EcCoreLib.s_dinter, ti)
        in PEapp(mk_loc op.pl_loc id, [e1; e2]) }

  | LPAREN; es = plist0(expr, COMMA); RPAREN
      { PEtuple es }

  | r = loc(RBOOL)
      { PEident (mk_loc r.pl_loc EcCoreLib.s_dbool, None) }

  | LPBRACE; fields = rlist1(expr_field, SEMICOLON); SEMICOLON?; RPBRACE
      { PErecord (None, fields) }

  | LPBRACE; b = sexpr; WITH; fields = rlist1(expr_field, SEMICOLON);
    SEMICOLON? RPBRACE
      { PErecord (Some b, fields) }

  | e = sexpr DOTTICK x = qident
      { PEproj (e, x) }

  | e = sexpr DOTTICK n = loc(word)
      { if n.pl_desc = 0 then
          error_message n.pl_loc
          (fun ppf ->
             Format.fprintf ppf "@[tuple@ projections@ start@ at@ 1@]");
        PEproji(e,n.pl_desc - 1) }

expr_u :
  | e = sexpr_u { e }

  | e = sexpr; args = sexpr+
       { PEapp (e, args) }

  | op = loc(uniop); ti = tvars_instan?; e = expr
       { peapp_symb op.pl_loc op.pl_desc ti [e] }

  | e = expr_chained_orderings %prec prec_below_order
       { fst e }

  | e1 = expr; op = loc(NE); ti = tvars_instan?; e2=expr
       { peapp_symb op.pl_loc "[!]" None
         [ mk_loc op.pl_loc (peapp_symb op.pl_loc "=" ti [e1; e2])] }

  | e1 = expr; op = loc(binop); ti = tvars_instan?; e2=expr
       { peapp_symb op.pl_loc op.pl_desc ti [e1; e2] }

  | c = expr; QUESTION; e1 = expr; COLON; e2 = expr; %prec LOP2
      { PEif (c, e1, e2) }

  | IF; c = expr; THEN; e1 = expr; ELSE; e2 = expr
      { PEif (c, e1, e2) }

  | MATCH; e = expr; WITH;
    PIPE?; bs = plist0(p = mcptn(sbinop); IMPL; be = expr { (p, be) }, PIPE);
    END
      { PEmatch (e, bs) }

  | LET; p = lpattern; EQ; e1 = expr; IN; e2 = expr
      { PElet (p, (e1, None), e2) }

  | LET; p = lpattern; COLON; ty = loc(type_exp); EQ; e1 = expr; IN; e2 = expr
      { PElet (p, (e1, Some ty), e2) }

  | r = loc(RBOOL); TILD; e = sexpr
       { let id  = PEident(mk_loc r.pl_loc EcCoreLib.s_dbitstring, None) in
         let loc = EcLocation.make $startpos $endpos in
         PEapp (mk_loc loc id, [e]) }

  | FUN; pd = ptybindings; IMPL; e = expr
  | FUN; pd = ptybindings; COMMA; e = expr { PElambda (pd, e) }

  | FORALL; pd = ptybindings; COMMA; e = expr { PEforall (pd, e) }
  | EXIST; pd = ptybindings; COMMA; e = expr { PEexists (pd, e) }

mcptn(BOP):
  | c = qoident; tvi = tvars_instan?; ps = bdident*
      { PPApp ((c, tvi), ps) }

  | LBRACKET; tvi = tvars_instan?; RBRACKET {
      let loc = EcLocation.make $startpos $endpos in
      PPApp ((pqsymb_of_symb loc EcCoreLib.s_nil, tvi), [])
    }

  | op = loc(uniop); tvi = tvars_instan?
      { PPApp ((pqsymb_of_symb op.pl_loc op.pl_desc, tvi), []) }

  | op = loc(uniop); tvi = tvars_instan? x = bdident
      { PPApp ((pqsymb_of_symb op.pl_loc op.pl_desc, tvi), [x]) }

  | x1 = bdident; op = loc(NE); tvi = tvars_instan?; x2 = bdident
      { PPApp ((pqsymb_of_symb op.pl_loc "[!]", tvi), [x1; x2]) }

  | x1 = bdident; op = loc(BOP); tvi = tvars_instan?; x2 = bdident
      { PPApp ((pqsymb_of_symb op.pl_loc op.pl_desc, tvi), [x1; x2]) }

  | x1 = bdident; op = loc(ordering_op); tvi = tvars_instan?; x2 = bdident
      { PPApp ((pqsymb_of_symb op.pl_loc op.pl_desc, tvi), [x1; x2]) }

expr_field :
  | x = qident; EQ; e = expr
      { { rf_name = x ; rf_tvi = None; rf_value = e; } }

expr_ordering :
  | e1 = expr; op = loc(ordering_op); ti = tvars_instan?; e2=expr
      { (op, ti, e1, e2) }

expr_chained_orderings :
  | e = expr_ordering
      { let (op, ti, e1, e2) = e in
        (peapp_symb op.pl_loc (unloc op) ti [e1; e2], e2) }

  | e1 = loc(expr_chained_orderings); op = loc(ordering_op);
    ti = tvars_instan?; e2 = expr
      { let (lce1, (e1, le)) = (e1.pl_loc, unloc e1) in
        let loc = EcLocation.make $startpos $endpos in
        (peapp_symb loc "&&" None
         [EcLocation.mk_loc lce1 e1;
          EcLocation.mk_loc loc
          (peapp_symb op.pl_loc (unloc op) ti [le; e2])],
         e2) }

pty_varty :
  | x = loc(bdident+)
      { (unloc x, mk_loc (loc x) PTunivar) }

  | x = bdident+ COLON ty = loc(type_exp)
      { (x, ty) }

%inline ptybinding1 :
  | LPAREN; bds = plist1(pty_varty, COMMA); RPAREN
      { bds }

  | x = loc(bdident)
      { [[unloc x], mk_loc (loc x) PTunivar] }

ptybindings :
  | x = ptybinding1+
      { List.flatten x }

  | x = bdident+; COLON; ty = loc(type_exp)
      { [x, ty] }

(* Localization *)

%inline loc(X)  :
  | x = X {
     { pl_desc = x;
       pl_loc  = EcLocation.make $startpos $endpos;
     }
   }

(* Parser Definitions *)

%inline plist0(X, S) :
  | aout = separated_list(S, X) { aout }

iplist1_r(X, S) :
  | x = X { [x] }
  | xs = iplist1_r(X, S); S; x = X { x :: xs }

%inline iplist1(X, S) :
  | xs = iplist1_r(X, S) { List.rev xs }

%inline plist1(X, S) :
  | aout = separated_nonempty_list(S, X) { aout }

%inline plist2(X, S) :
  | x = X; S; xs = plist1(X, S) { x :: xs }

%inline list2(X) :
  | x = X; xs = X+ { x :: xs }

%inline empty :
  | /**/ { () }

(* -------------------------------------------------------------------- *)
__rlist1(X, S):                         (* left-recursive *)
  | x = X { [x] }
  | xs = __rlist1(X, S); S; x = X { x :: xs }

%inline rlist0(X, S) :
  | /* empty */     { [] }
  | xs = rlist1(X, S) { xs }

%inline rlist1(X, S) :
  | xs = __rlist1(X, S) { List.rev xs }

%inline rlist2(X, S) :
  | xs = __rlist1(X, S); S; x = X { List.rev (x :: xs) }

(* -------------------------------------------------------------------- *)
%inline paren(X) :
  | LPAREN; x = X; RPAREN { x }

%inline brace(X) :
  | LBRACE; x = X; RBRACE { x }

%inline bracket(X) :
  | LBRACKET; x = X; RBRACKET { x }

(* -------------------------------------------------------------------- *)
%inline seq(X, Y) :
  | x = X; y = Y { (x, y) }

%inline prefix(S, X) :
  | S; x = X { x }

%inline postfix(X, S) :
  | x = X; S { x }

%inline sep(S1, X, S2) :
  | x = S1; X; y = S2 { (x, y) }

%inline either(X, Y) :
  | X {}
  | Y {}

(* UcSpec module *)

(* Specification Parse Trees

   This includes parse trees for specifications of functionalities,
   simulators and associated interfaces, but also for user input to
   the interpreter. *)

(* specification of symbols, types and expressions borrowed from
   src/ecParsetree.ml of EasyCrypt distribution *)

open EcLocation
open EcSymbols
open EcBigInt
open UcSpecTypedSpecCommon

(* symbols *)

let qsymb_of_symb (x : symbol) : qsymbol = ([], x)

type pqsymbol  = qsymbol located
type osymbol_r = psymbol option
type osymbol   = osymbol_r located

(* types *)

type pty_r =
  | PTunivar
  | PTtuple of pty list
  | PTnamed of pqsymbol
  | PTvar   of psymbol
  | PTapp   of pqsymbol * pty list
  | PTfun   of pty * pty
and pty = pty_r located

(* type variable instantiations *)

type ptyinstan_r =
  | TVIunamed of pty list
  | TVInamed  of (psymbol * pty) list

and ptyinstan  = ptyinstan_r located

(* expressions *)

type plpattern_r =
  | LPSymbol of psymbol
  | LPTuple  of osymbol list
  | LPRecord of (pqsymbol * psymbol) list

and plpattern = plpattern_r located

type ppattern =
  | PPApp of (pqsymbol * ptyinstan option) * osymbol list

type ptybinding  = osymbol list * pty
and  ptybindings = ptybinding list

and pexpr_r =
  | PEcast    of pexpr * pty                       (* type cast          *)
  | PEint     of zint                              (* int. literal       *)
  | PEdecimal of (zint * (int * zint))             (* dec. literal       *)
  | PEident   of pqsymbol * ptyinstan option       (* symbol             *)
  | PEapp     of pexpr * pexpr list                (* op. application    *)
  | PElet     of plpattern * pexpr_wty * pexpr     (* let binding        *)
  | PEtuple   of pexpr list                        (* tuple constructor  *)
  | PEif      of pexpr * pexpr * pexpr             (* _ ? _ : _          *)
  | PEmatch   of pexpr * (ppattern * pexpr) list   (* match              *)
  | PEforall  of ptybindings * pexpr               (* forall quant.      *)
  | PEexists  of ptybindings * pexpr               (* exists quant.      *)
  | PElambda  of ptybindings * pexpr               (* lambda abstraction *)
  | PErecord  of pexpr option * pexpr rfield list  (* record             *)
  | PEproj    of pexpr * pqsymbol                  (* projection         *)
  | PEproji   of pexpr * int                       (* tuple projection   *)
  | PEscope   of pqsymbol * pexpr                  (* scope selection    *)

and pexpr = pexpr_r located
and pexpr_wty = pexpr * pty option

and 'a rfield = {
  rf_name  : pqsymbol;
  rf_tvi   : ptyinstan option;
  rf_value : 'a;
}

(* type bindings *)

type type_binding =
  {id : psymbol;  (* identifier *)
   ty : pty}      (* its type *)

(* messages *)

type message_body =
  {id     : psymbol;            (* name of message *)
   params : type_binding list}  (* typed parameters *)

type message_def =
  {dir    : msg_dir;            (* message direction *)
   id     : psymbol;            (* name of message *)
   params : type_binding list;  (* typed parameters *)
   port   : psymbol option}     (* optional port name -
                                   used in EasyCrypt code generation *)

(* interfaces: basic and composite; direct and adversarial *)

(* the components of composite interfaces are required to be basic
   ones *)

type comp_item =
  {sub_id   : psymbol;  (* name of component *)
   inter_id : psymbol}  (* name of basic interface - interpreted
                           in the same root (of .uc file) *)

type inter =
  | Basic     of message_def list  (* basic interface *)
  | Composite of comp_item list    (* composite interface *)

type named_inter =
  {id    : psymbol;  (* name of interface *)
   inter : inter}    (* contents of interface *)

type inter_def =
  | DirectInter      of named_inter  (* direct interface *)
  | AdversarialInter of named_inter  (* adversarial interface *)

(* state machines *)

(* message and state expressions *)

type msg_expr =
  {path      : msg_path;            (* message path *)
   args      : pexpr list located;  (* message arguments *)
   port_expr : pexpr option}        (* message destination - port expr *)

type state_expr =
  {id   : psymbol;             (* state to transition to *)
   args : pexpr list located}  (* arguments of new state *)

(* instructions *)

type send_and_transition =
  {msg_expr   : msg_expr;    (* message to send *)
   state_expr : state_expr}  (* state to transition to *)

type instruction_u =
  | Assign of lhs * pexpr                       (* ordinary assignment *)
  | Sample of lhs * pexpr                       (* sampling assignment *)
  | ITE of pexpr * instruction list located *   (* if-then-else *)
           instruction list located option
  | Match of pexpr * match_clause list located  (* match instruction *)
  | SendAndTransition of send_and_transition    (* send and transition *)
  | Fail                                        (* failure *)

and instruction = instruction_u located

and match_clause = ppattern * instruction list located

let isUnconditionalFailure (ill : instruction list located) =
  match (unloc ill) with
  | [instr] ->
      (match (unloc instr) with
       | Fail -> true
       | _    -> false)
  | _       -> false

(* state machines *)

type msg_match_clause =                 (* message match clause *)
  {msg_pat : symbol msg_pat;            (* message pattern *)
   code    : instruction list located}  (* code of clause *)

type state_code =
  {vars      : type_binding list;      (* typed local variables *)
   mmclauses : msg_match_clause list}  (* message match clauses *)

type state =
  {id     : psymbol;                    (* name of state *)
   params : type_binding list located;  (* typed state parameters *)
   code   : state_code}                 (* code of state *)
                
type state_def =  (* state definition *)
  | InitialState of state
  | FollowingState of state 

(* functionalities and simulators *)

type party_def =
  {id     : psymbol;         (* name of party *)
   serves : pqsymbol list;   (* interfaces served *)
   states : state_def list}  (* state machine *)

type sub_fun_decl =     (* subfunctionality definition *)
  {id      : psymbol;   (* name of subfunctionality *)
   fun_qid : pqsymbol}  (* qualified name of ideal functionality *)

type fun_body_real =                   (* real functionality body *)
  {sub_fun_decls : sub_fun_decl list;  (* sub-functionalities *)
   party_defs    : party_def list}     (* party defintions *)

type fun_body =                     (* functionality body *)
  | FunBodyReal  of fun_body_real   (* real functionality *)
  | FunBodyIdeal of state_def list  (* ideal funcitonality *)

let is_real_fun_body (fb : fun_body) : bool =
  match fb with
  | FunBodyReal _  -> true
  | FunBodyIdeal _ -> false

type fun_param =        (* functionality parameter *)
  {id      : psymbol;   (* name of parameter to functionality *)
   dir_qid : pqsymbol}  (* qualified name of composite direct interface *)

type fun_def =                 (* functionality definition *)
  {id       : psymbol;         (* name of functionality *)
   params   : fun_param list;  (* parameters to functionality *)
   dir_id   : psymbol;         (* name of composite direct interface,
                                  interpreted in same root *)
   adv_id   : psymbol option;  (* optional name of adversarial interface,
                                  interpreted in same root *)
   fun_body : fun_body}        (* functionality body *)

type sim_def =                             (* simulator definition *)
  {id            : psymbol;                (* name of simulator *)
   uses          : psymbol;                (* name of basic adversarial
                                              interface (from ideal
                                              functionality),
                                              interpreted in same root *)
   sims          : psymbol;                (* name of real functionality
                                              being simulated, interpreted
                                              in same root *)
   sims_arg_qids : pqsymbol list located;  (* qualified names of ideal
                                              functionality arguments to
                                              simulated real functionalities *)
   states        : state_def list }        (* state machine *)

(* top-level defintions *)

type def =
  | InterDef of inter_def  (* interface *)
  | FunDef   of fun_def    (* functionality *)
  | SimDef   of sim_def    (* simulator *)

(* UC and EasyCrypt requires *)

type externals =
  {uc_requires : psymbol list;           (* require .uc files *)
   ec_requires : (psymbol * bool) list}  (* require and optionally import
                                            .ec files; true means import *)

(* overall UC specifications *)

type spec =
  {externals   : externals;
   definitions : def list}

(* functionality expression

   when a functionality has "()" as its argument list, we use
   FunExprArgs (with []), but if it has no argument list, we use
   FunExprNoArgs

   in typechecking, we will forbid ideal functionalities with an
   empty argument list, insisting on form FunExprNoArgs *)

type fun_expr =
  | FunExprNoArgs of pqsymbol
  | FunExprArgs   of pqsymbol * fun_expr list

let loc_of_fun_expr (fe : fun_expr) : EcLocation.t =
  match fe with
  | FunExprNoArgs pqsym    -> loc pqsym
  | FunExprArgs (pqsym, _) -> loc pqsym

(* for use in sent message expr *)

type port_or_addr_pexpr =
  | PoA_Port of pexpr
  | PoA_Addr of pexpr

(* expression for message in transit

   message path must be qualified by root, as otherwise could
   be ambiguous

   origin or destination can be an address, when the port index
   is implicit from the message path

   when it's the *origin* whose port index is being inferred, this
   will be true iff the message direction is "out" and either the
   message path terminates in a component of a composite interface or
   terminates with the basic adversarial interface of an ideal
   functionality

   when it's the *destination* whose port index is being inferred,
   this will be true iff the message direction is "in" and either the
   message path terminates in a component of a composite interface or
   terminates with the basic adversarial interface of an ideal
   functionality *)

type sent_msg_expr =
  {in_poa_pexpr  : port_or_addr_pexpr;  (* source *)
   path          : msg_path;            (* message path *)
   args          : pexpr list located;  (* message arguments *)
   out_poa_pexpr : port_or_addr_pexpr}  (* destination *)

(* prover command *)

type include_exclude = [ `Include | `Exclude ]

type pdbmap1 = {
  pht_flag : include_exclude;
  pht_kind : [ `Theory  | `Lemma   ];
  pht_name : pqsymbol;
}

and pdbhint = pdbmap1 list

type pprover_list = {
  pp_use_only : string located list;
  pp_add_rm   : (include_exclude * string located) list;
}

let empty_pprover_list = {
  pp_use_only = [];
  pp_add_rm   = [];
}

type pprover_infos = {
  pprov_max       : int option;
  pprov_timeout   : int option;
  pprov_cpufactor : int option;
  pprov_names     : pprover_list option;
  pprov_quorum    : int option;
  pprov_verbose   : int option option;
  pprov_version   : [`Lazy | `Full] option;
  plem_all        : bool option;
  plem_max        : int option option;
  plem_iterate    : bool option;
  plem_wanted     : pdbhint option;
  plem_unwanted   : pdbhint option;
  plem_dumpin     : string located option;
  plem_selected   : bool option;
  psmt_debug      : bool option;
}

(* Interpreter User Input *)

type world =
  | Real
  | Ideal

type interpreter_command_u =
  | Load of psymbol
  | Funex of fun_expr
  | World of world
  | Send of sent_msg_expr
  | Run
  | Step
  | Addv of type_binding (*TODO add to parser*)
  | Addf of psymbol * pexpr (*TODO add to parser*)
  | Prover of pprover_infos (*TODO add to interpreter client*)
  | Back of int located (*TODO add to interpreter client*)
  | Finish
  | Quit

type interpreter_command = interpreter_command_u located

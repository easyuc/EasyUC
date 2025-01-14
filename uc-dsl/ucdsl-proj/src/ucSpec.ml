(* UcSpec module *)

(* Specification Parse Trees

   This includes parse trees for specifications of functionalities,
   simulators and associated interfaces, but also for user input to
   the interpreter.

   We use EasyCrypt's parse trees for types (pty) and formulas
   (pformula).

   We still talk about "expressions" in the UC DSL, even though they
   are represented as formulas. They are the subset of formulas
   described by our grammar (see nonterminal `expr` of
   ucParser.mly). *)

open EcLocation
open EcSymbols
open EcParsetree
open UcSpecTypedSpecCommon

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
  {sub_id   : psymbol;  (* name of sub-interface *)
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
  {path      : msg_path;               (* message path *)
   args      : pformula list located;  (* message arguments *)
   port_expr : pformula option}        (* message destination - port expr *)

type state_expr =
  {id   : psymbol;                (* state to transition to *)
   args : pformula list located}  (* arguments of new state *)

(* instructions *)

type send_and_transition =
  {msg_expr   : msg_expr;    (* message to send *)
   state_expr : state_expr}  (* state to transition to *)

type instruction_u =
  | Assign of lhs * pformula                       (* ordinary assignment *)
  | Sample of lhs * pformula                       (* sampling assignment *)
  | ITE of pformula * instruction list located *   (* if-then-else *)
           instruction list located option
  | Match of pformula * match_clause list located  (* match instruction *)
  | SendAndTransition of send_and_transition       (* send and transition *)
  | Fail                                           (* failure *)

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

type port_or_addr =
  | PoA_Port of pformula
  | PoA_Addr of pformula

let loc_of_port_or_addr (poa : port_or_addr) : EcLocation.t =
  match poa with
  | PoA_Port pformula -> loc pformula
  | PoA_Addr pformula -> loc pformula

(* expression for message in transit (sent message expession)

   there are two forms, ordinary and for environment/adversary
   communication

   -- ordinary --

   message path must be qualified by root, as otherwise could
   be ambiguous

   source or destination can be an address, when the port index
   is implicit from the message path

   when it's the *source* whose port index is being inferred, this
   will be possible iff the message direction is "out" and either the
   message path terminates in a component of a composite interface or
   terminates with the basic adversarial interface of an ideal
   functionality

   when it's the *destination* whose port index is being inferred,
   this will be possible iff the message direction is "in" and either the
   message path terminates in a component of a composite interface or
   terminates with the basic adversarial interface of an ideal
   functionality

   -- environment/adversary communication --

   this form carries no data, and has both source and destination ports.
   its function is to model whatever communication the environment
   and adversary are carrying out (which would pass data) *)

type sent_msg_expr_ord =
  {src_poa  : port_or_addr;           (* source *)
   path     : msg_path;               (* message path *)
   args     : pformula list located;  (* message arguments *)
   dest_poa : port_or_addr}           (* destination *)

type sent_msg_expr_env_adv =
  {src_port  : pformula;   (* source *)
   dest_port : pformula }  (* destination *)

type sent_msg_expr =
  | SME_Ord    of sent_msg_expr_ord
  | SME_EnvAdv of sent_msg_expr_env_adv

let loc_of_src_of_sent_msg_expr (sme : sent_msg_expr) : EcLocation.t =
  match sme with
  | SME_Ord sme    -> loc_of_port_or_addr sme.src_poa
  | SME_EnvAdv sme -> loc sme.src_port

let loc_of_dest_of_sent_msg_expr (sme : sent_msg_expr) : EcLocation.t =
  match sme with
  | SME_Ord sme    -> loc_of_port_or_addr sme.dest_poa
  | SME_EnvAdv sme -> loc sme.dest_port

(* rewriting databases modification *)

(* the first component is what should be removed; the second
   component is what should then be added *)

type mod_dbs = pqsymbol list * pqsymbol list

(* Interpreter User Input *)

type world =
  | Real
  | Ideal

type control =
  | CtrlEnv
  | CtrlAdv

type peffect_r =
  | EffectOK
  | EffectRand
  | EffectMsgOut of sent_msg_expr * control
  | EffectFailOut

type peffect = peffect_r located

type interpreter_command_u =
  | Load   of psymbol
  | FunEx  of fun_expr
  | World  of world
  | Send   of sent_msg_expr
  | Run
  | Step   of EcParsetree.pprover_infos option * mod_dbs option
  | AddVar of type_binding
  | AddAss of psymbol * pformula
  | Prover of EcParsetree.pprover_infos
  | Hint   of mod_dbs
  | Finish
  | Assert of peffect
  | Debug
  | Undo   of int located
  | Quit

type interpreter_command = interpreter_command_u located

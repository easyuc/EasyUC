(* UcSpec module *)

(* Specification Parse Trees *)

(* specification of symbols, types and expressions borrowed from
   src/ecParsetree.ml of EasyCrypt distribution, which has copyright: *)

(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2018 - Inria
 * Copyright (c) - 2012--2018 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

(* --------------------------------------------------------------------
 * Copyright (c) - 2020-2021 - Boston University
 *
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

open EcLocation
open UcSpecTypedSpecCommon
open UcMessage

let parse_error = error_message

let type_error = error_message

let type_warning = warning_message


(* type bindings *)

type type_binding =
  {id : psymbol;  (* identifier *)
   ty : pty}      (* its type *)

(* messages *)

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
  {msg_pat : msg_pat;                   (* message pattern *)
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

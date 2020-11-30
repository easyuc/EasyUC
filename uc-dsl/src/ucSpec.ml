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
 * Copyright (c) - 2020 - Boston University
 *
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

open EcBigInt
open EcLocation
open EcSymbols
open UcMessage

let parse_error = error_message

let type_error = error_message

(* symbols *)

let qsymb_of_symb (x : symbol) : qsymbol = ([], x)

type psymbol   = symbol  located
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

type ptyannot_r =
  | TVIunamed of pty list
  | TVInamed  of (psymbol * pty) list

and ptyannot  = ptyannot_r located

(* expressions *)

type plpattern_r =
  | LPSymbol of psymbol
  | LPTuple  of osymbol list
  | LPRecord of (pqsymbol * psymbol) list

and plpattern = plpattern_r located

type ppattern =
  | PPApp of (pqsymbol * ptyannot option) * osymbol list

type ptybinding  = osymbol list * pty
and  ptybindings = ptybinding list

and pexpr_r =
  | PEcast   of pexpr * pty                       (* type cast          *)
  | PEint    of zint                              (* int. literal       *)
  | PEdecimal of (zint * (int * zint))             (* dec. literal       *)
  | PEident  of pqsymbol * ptyannot option        (* symbol             *)
  | PEapp    of pexpr * pexpr list                (* op. application    *)
  | PElet    of plpattern * pexpr_wty * pexpr     (* let binding        *)
  | PEtuple  of pexpr list                        (* tuple constructor  *)
  | PEif     of pexpr * pexpr * pexpr             (* _ ? _ : _          *)
  | PEmatch  of pexpr * (ppattern * pexpr) list   (* match              *)
  | PEforall of ptybindings * pexpr               (* forall quant.      *)
  | PEexists of ptybindings * pexpr               (* exists quant.      *)
  | PElambda of ptybindings * pexpr               (* lambda abstraction *)
  | PErecord of pexpr option * pexpr rfield list  (* record             *)
  | PEproj   of pexpr * pqsymbol                  (* projection         *)
  | PEproji  of pexpr * int                       (* tuple projection   *)
  | PEscope  of pqsymbol * pexpr                  (* scope selection    *)

and pexpr = pexpr_r located
and pexpr_wty = pexpr * pty option

and 'a rfield = {
  rf_name  : pqsymbol;
  rf_tvi   : ptyannot option;
  rf_value : 'a;
}

(* type bindings *)

type type_binding = {id : psymbol; ty : pty}

(* messages *)

type msg_dir =
  | In
  | Out

let invert_dir (dir : msg_dir) = 
  match dir with In -> Out | Out -> In

type message_body =
  {id : psymbol; params : type_binding list}

type message_def =
  {dir : msg_dir; id : psymbol; params : type_binding list;
   port : psymbol option}

(* interfaces *)

type comp_item = {sub_id : psymbol; inter_id : psymbol}

type inter =
  | Basic     of message_def list
  | Composite of comp_item list

type named_inter = {id : psymbol; inter : inter}

type inter_def =
  | DirectInter      of named_inter
  | AdversarialInter of named_inter

(* message patterns and message paths *)

type msg_or_star =
  | MsgOrStarMsg of symbol
  | MsgOrStarStar

type msg_path_pat_u = {inter_id_path : symbol list; msg_or_star : msg_or_star}

type msg_path_pat = msg_path_pat_u located

let msg_path_pat_ends_star mpp =
  match (unloc mpp).msg_or_star with
  | MsgOrStarMsg  _ -> false
  | MsgOrStarStar   -> true

type pat =
  | PatId       of psymbol
  | PatWildcard of EcLocation.t

let get_loc_pat (pat : pat) : EcLocation.t = 
  match pat with
  | PatWildcard l -> l
  | PatId id      -> loc id

let get_loc_pat_list (tm : pat list) : EcLocation.t =
  mergeall (List.map (fun mi -> get_loc_pat mi) tm)

type msg_pat =
  {port_id : psymbol option; msg_path_pat : msg_path_pat;
   pat_args : pat list option}

type msg_pat_body =
  {msg_path_pat : msg_path_pat; pat_args : pat list option}

type msg_path_u = {inter_id_path : symbol list; msg : symbol}

type msg_path = msg_path_u located

(* message and state expressions *)

type msg_expr =
  {path : msg_path; args : pexpr list located; port_expr : pexpr option}

type state_expr = {id : psymbol; args : pexpr list located}

(* instructions *)

type send_and_transition = {msg_expr : msg_expr; state_expr : state_expr}

type lhs =  (* left-hand sides *)
  | LHSSimp  of psymbol
  | LHSTuple of psymbol list

type instruction_u =
  | Assign of lhs * pexpr
  | Sample of lhs * pexpr
  | ITE of pexpr * instruction list located *  (* if-then-else *)
           instruction list located option
  | Match of pexpr * match_clause list located
  | SendAndTransition of send_and_transition
  | Fail

and instruction = instruction_u located

and match_clause = ppattern * instruction list located

(* state machines *)

type msg_match_clause = {msg_pat : msg_pat; code : instruction list located}

type state_code = {vars : type_binding list; mmclauses : msg_match_clause list}

type state =
  {id : psymbol; params : type_binding list located; code : state_code}
                
type state_def =
  | InitialState of state
  | FollowingState of state 

(* functionalities and simulators *)

type party_def =
  {id : psymbol; serves : pqsymbol list; states : state_def list}

type sub_fun_decl = {id : psymbol; fun_id : psymbol}

type fun_body_real =
  {sub_fun_decls : sub_fun_decl list; party_defs : party_def list}

type fun_body =
  | FunBodyReal  of fun_body_real
  | FunBodyIdeal of state_def list

let is_real_fun_body fb =
  match fb with
  | FunBodyReal _  -> true
  | FunBodyIdeal _ -> false

type fun_param = {id : psymbol; id_dir : psymbol}

type fun_def =
  {id : psymbol; params : fun_param list; id_dir : psymbol;
   id_adv : psymbol option; fun_body : fun_body}

type sim_def =
  {id : psymbol; uses : psymbol; sims : psymbol;
   sims_arg_ids : psymbol list located; states : state_def list }

(* top-level defintions *)

type def =
  | InterDef of inter_def
  | FunDef   of fun_def
  | SimDef   of sim_def

(* UC and EasyCrypt requires *)

type externals = {uc_requires : psymbol list; ec_requires : psymbol list}

(* overall UC specifications *)

type spec = {externals : externals; definitions : def list}

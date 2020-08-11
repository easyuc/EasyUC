(* UcTypedSpec module *)

(* Typed Specifications *)

open EcLocation
open UcTypes
open UcSpec

module IdMap = Map.Make(String)
module IdSet = Set.Make(String)
module SL = 
  struct
    type t = string list
    let compare = Pervasives.compare
  end
module QidMap = Map.Make(SL)
module QidSet = Set.Make(SL)

let exists_id (id_map : 'a IdMap.t) (id : string) : bool = 
  IdMap.exists (fun key _ -> key = id) id_map

type typ_tyd = (typ * int) located

type message_def_body_tyd =
  {dir : msg_dir; params_map : typ_tyd IdMap.t; port : id option}

type basic_inter_body_tyd = (message_def_body_tyd located) IdMap.t

type inter_body_tyd = 
  | BasicTyd     of basic_inter_body_tyd
  | CompositeTyd of id IdMap.t

let is_basic_tyd ibt =
  match ibt with
  | BasicTyd _     -> true
  | CompositeTyd _ -> false

let is_composite_tyd ibt =
  match ibt with
  | BasicTyd _     -> false
  | CompositeTyd _ -> true

type inter_tyd = inter_body_tyd located

type state_body_tyd =
  {is_initial : bool; params : typ_tyd IdMap.t; vars : typ located IdMap.t;
   mmclauses : msg_match_clause list}

type state_tyd = state_body_tyd located

type party_def_body_tyd =
  {serves : string list located list; states : state_tyd IdMap.t}

type party_def_tyd = party_def_body_tyd located

type real_fun_body_tyd =
  {params       : (id * int) IdMap.t;
   id_dir_inter : string;
   id_adv_inter : string option;
   sub_funs     : id IdMap.t;  (* names of ideal functionalities *)
   parties      : party_def_tyd IdMap.t}

type ideal_fun_body_tyd =
  {id_dir_inter : string;
   id_adv_inter : string;
   states       : state_tyd IdMap.t}

type fun_body_tyd =
  | FunBodyRealTyd  of real_fun_body_tyd
  | FunBodyIdealTyd of ideal_fun_body_tyd

let is_real_fun_body_tyd fb =
  match fb with
  | FunBodyRealTyd _  -> true
  | FunBodyIdealTyd _ -> false

let params_of_fun_body_tyd f =
  match f with
  | FunBodyRealTyd fbr -> fbr.params
  | FunBodyIdealTyd _  -> IdMap.empty

let id_dir_io_of_fun_body_tyd f =
  match f with
  | FunBodyRealTyd fbr  -> fbr.id_dir_inter
  | FunBodyIdealTyd fbi -> fbi.id_dir_inter

let id_adv_io_of_fun_body_tyd f =
  match f with
  | FunBodyRealTyd fbr  -> fbr.id_adv_inter
  | FunBodyIdealTyd fbi -> Some fbi.id_adv_inter

let sub_funs_of_fun_body_tyd f =
  match f with
  | FunBodyRealTyd fbr -> fbr.sub_funs
  | FunBodyIdealTyd _  -> IdMap.empty

let parties_of_fun_body_tyd f =
  match f with
  | FunBodyRealTyd fbr -> fbr.parties
  | FunBodyIdealTyd _  -> IdMap.empty

let states_of_fun_body_tyd f =
  match f with
  | FunBodyRealTyd _    -> IdMap.empty
  | FunBodyIdealTyd fbi -> fbi.states

type fun_tyd = fun_body_tyd located

type sim_body_tyd =
  {uses : string; sims : string; sims_arg_ids :  string list;
   states : state_tyd IdMap.t}

type sim_def_tyd = sim_body_tyd located

type typed_spec =
  { direct_inters      : inter_tyd IdMap.t;
    adversarial_inters : inter_tyd IdMap.t;
    functionalities    : fun_tyd IdMap.t;
    simulators         : sim_def_tyd IdMap.t;
  }

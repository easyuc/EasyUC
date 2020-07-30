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
module QidSet = Set.Make(SL)
module QidMap = Map.Make(SL)

let exists_id (id_map : 'a IdMap.t) (id : string) : bool = 
  IdMap.exists (fun key _ -> key = id) id_map

type typ_tyd = (typ * int) located

type message_def_body =
  {direction : msg_dir; content : typ_tyd IdMap.t; port_label : id option}

type basic_inter_body_tyd = (message_def_body located) IdMap.t

type comp_item_tyd = id located

type inter_body_tyd = 
  | Basic     of basic_inter_body_tyd
  | Composite of comp_item_tyd IdMap.t

type inter_tyd = inter_body_tyd located

type state_body =
  {is_initial : bool; params : typ_tyd IdMap.t; vars : typ located IdMap.t;
   mmclauses : msg_match_clause list}

type state_tyd = state_body located

type sub_fun_decl_body = {fun_id : string}

type sub_fun_decl_tyd = sub_fun_decl_body located

type party_def_body =
  {serves : string list located list; states : state_tyd IdMap.t}

type party_def_tyd = party_def_body located

type real_fun_body =
  {params    : (comp_item_tyd * int) IdMap.t;
   id_dir_io : string;
   id_adv_io : string option;
   sub_funs  : sub_fun_decl_tyd IdMap.t;
   parties   : party_def_tyd IdMap.t}

type ideal_fun_body =
  {id_dir_io : string;
   id_adv_io : string;
   states    : state_tyd IdMap.t}

type fun_body_tyd =
  | FunBodyReal of real_fun_body
  | FunBodyIdeal of ideal_fun_body

let is_real_fun_body_tyd fb =
  match fb with
  | FunBodyReal _  -> true
  | FunBodyIdeal _ -> false

let params_of_fun_body_tyd f =
  match f with
  | FunBodyReal fbr -> fbr.params
  | FunBodyIdeal _  -> IdMap.empty

let id_dir_io_of_fun_body_tyd f =
  match f with
  | FunBodyReal fbr  -> fbr.id_dir_io
  | FunBodyIdeal fbi -> fbi.id_dir_io

let id_adv_io_of_fun_body_tyd f =
  match f with
  | FunBodyReal fbr  -> fbr.id_adv_io
  | FunBodyIdeal fbi -> Some fbi.id_adv_io

let sub_funs_of_fun_body_tyd f =
  match f with
  | FunBodyReal fbr -> fbr.sub_funs
  | FunBodyIdeal _  -> IdMap.empty

let parties_of_fun_body_tyd f =
  match f with
  | FunBodyReal fbr -> fbr.parties
  | FunBodyIdeal _  -> IdMap.empty

let states_of_fun_body_tyd f =
  match f with
  | FunBodyReal _    -> IdMap.empty
  | FunBodyIdeal fbi -> fbi.states

type fun_tyd = fun_body_tyd located

type sim_body =
  {uses : string; sims : string; sims_arg_ids :  string list;
   states : state_tyd IdMap.t}

type sim_def_tyd = sim_body located

type typed_spec =
  { direct_ios       : inter_tyd IdMap.t;
    adversarial_ios  : inter_tyd IdMap.t;
    functionalities  : fun_tyd IdMap.t;
    simulators       : sim_def_tyd IdMap.t;
  }

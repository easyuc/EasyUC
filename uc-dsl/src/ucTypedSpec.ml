(* UcTypedSpec module *)

(* Typed Specifications *)

open EcLocation
open EcSymbols
open EcTypes
open UcSpec

(* id maps and sets *)

module IdMap = Map.Make(String)

let exists_id (id_map : 'a IdMap.t) (id : string) : bool = 
  IdMap.exists (fun key _ -> key = id) id_map

module IdSet = Set.Make(String)

module SL = 
  struct
    type t = string list
    let compare = Pervasives.compare
  end
module QidMap = Map.Make(SL)
module QidSet = Set.Make(SL)

let get_keys_as_sing_qids (m : 'a IdMap.t) : QidSet.t = 
  let ids = fst (List.split (IdMap.bindings m)) in
  QidSet.of_list (List.map (fun id -> [id]) ids)

let indexed_map_to_list (mapind : ('o * int) IdMap.t) : 'o list =
  let l = IdMap.fold (fun _ v l -> v :: l ) mapind [] in
  let lord = List.sort (fun a1 a2 -> snd a1 - snd a2) l in
  List.map (fun a -> fst a) lord

let filter_map (fm : 'a -> 'b option) (m : 'a IdMap.t) : 'b IdMap.t =
  let flt =
    IdMap.filter
    (fun _ def ->
       match fm def with
       | Some _ -> true
       | None   -> false)
    m in
  IdMap.map
  (fun def ->
     match fm def with
     | Some x -> x
     | None -> raise (Failure "!impossible!"))
  flt

let unlocm (lm : 'a located IdMap.t) : 'a IdMap.t =
  IdMap.map (fun al -> unloc al) lm

type ty_index = (ty * int) located

type lsymbol = symbol located

type message_def_body_tyd =
  {dir : msg_dir; params_map : ty_index IdMap.t; port : lsymbol option}

type basic_inter_body_tyd = (message_def_body_tyd located) IdMap.t

(* inversion of direction *)

let invert_msg_dir (mdbt : message_def_body_tyd) : message_def_body_tyd = 
  {mdbt with
     dir = invert_dir mdbt.dir}

let invert_msg_dir_loc
    (mdbtl : message_def_body_tyd located) : message_def_body_tyd located = 
  let l = loc mdbtl in
  let mdbt = unloc mdbtl in
  let mdbt_inv = invert_msg_dir mdbt in
  mk_loc l mdbt_inv

let invert_basic_inter_body_tyd
    (bibt : basic_inter_body_tyd) : basic_inter_body_tyd = 
  IdMap.map invert_msg_dir_loc bibt

type inter_body_tyd = 
  | BasicTyd     of basic_inter_body_tyd
  | CompositeTyd of lsymbol IdMap.t

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
  {is_initial : bool; params : ty_index IdMap.t; vars : ty located IdMap.t;
   mmclauses : msg_match_clause list}

type state_tyd = state_body_tyd located

type party_def_body_tyd =
  {serves : string list located list; states : state_tyd IdMap.t}

type party_def_tyd = party_def_body_tyd located

type real_fun_body_tyd =
  {params       : (lsymbol * int) IdMap.t;
   id_dir_inter : string;
   id_adv_inter : string option;
   sub_funs     : lsymbol IdMap.t;  (* names of ideal functionalities *)
   parties      : party_def_tyd IdMap.t}

type ideal_fun_body_tyd =
  {id_dir_inter : string;
   id_adv_inter : string;
   states       : state_tyd IdMap.t}

type fun_body_tyd =
  | FunBodyRealTyd  of real_fun_body_tyd
  | FunBodyIdealTyd of ideal_fun_body_tyd

let real_fun_body_tyd_of fbt =
  match fbt with
  | FunBodyRealTyd rfbt -> rfbt
  | FunBodyIdealTyd _   -> UcMessage.failure "cannot happen"

let ideal_fun_body_tyd_of fbt =
  match fbt with
  | FunBodyRealTyd _     ->  UcMessage.failure "cannot happen" 
  | FunBodyIdealTyd ifbt -> ifbt

let is_real_fun_body_tyd fb =
  match fb with
  | FunBodyRealTyd _  -> true
  | FunBodyIdealTyd _ -> false

let id_dir_inter_of_fun_body_tyd f =
  match f with
  | FunBodyRealTyd fbr  -> fbr.id_dir_inter
  | FunBodyIdealTyd fbi -> fbi.id_dir_inter

let id_adv_inter_of_fun_body_tyd f =
  match f with
  | FunBodyRealTyd fbr  -> fbr.id_adv_inter
  | FunBodyIdealTyd fbi -> Some fbi.id_adv_inter

type fun_tyd = fun_body_tyd located

type sim_body_tyd =
  {uses : string; sims : string; sims_arg_ids :  string list;
   states : state_tyd IdMap.t}

type sim_def_tyd = sim_body_tyd located

(* four identifier (technically, unlocated identifier) maps for direct
   and adversarial interfaces, functionalities and simulators; their
   domains are disjoint *)

type maps_tyd =
  {dir_inter_map : inter_tyd IdMap.t;
   adv_inter_map : inter_tyd IdMap.t;
   fun_map       : fun_tyd IdMap.t;
   sim_map       : sim_def_tyd IdMap.t}

let exists_id_maps_tyd (maps : maps_tyd) (uid : string) =
  exists_id maps.dir_inter_map uid ||
  exists_id maps.adv_inter_map uid ||
  exists_id maps.fun_map uid ||
  exists_id maps.sim_map uid

let exists_id_inter_maps
    (dir_inter_map : inter_tyd IdMap.t) (adv_inter_map : inter_tyd IdMap.t)
    (uid : string) : bool =
  exists_id dir_inter_map uid || exists_id adv_inter_map uid

type typed_spec =
  {required_maps : maps_tyd;  (* from uc_requires *)
   current_maps  : maps_tyd}  (* from current file *)

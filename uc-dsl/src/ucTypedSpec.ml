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

type basic_io_body_tyd = (message_def_body located) IdMap.t

type comp_item_tyd = id located

type io_body_tyd = 
  | Basic of basic_io_body_tyd
  | Composite of comp_item_tyd IdMap.t

type io_tyd = io_body_tyd located

type state_body =
  {is_initial : bool; params : typ_tyd IdMap.t; vars : typ located IdMap.t;
   mmcodes : msg_match_code list}

type state_tyd = state_body located

type sub_fun_decl_body = {fun_id : string; fun_param_ids : id list}

type sub_fun_decl_tyd = sub_fun_decl_body located

type party_def_body =
  {serves : string list located list; code :  state_tyd IdMap.t}

type party_def_tyd = party_def_body located

(*either states is an empty map or both sub_funs and parties are empty maps*)
type fun_body =
  {params : (comp_item_tyd * int) IdMap.t; id_dir_io : string;
   id_adv_io : string option; sub_funs :  sub_fun_decl_tyd IdMap.t;
   parties :  party_def_tyd IdMap.t; states :  state_tyd IdMap.t}

type fun_tyd = fun_body located

type sim_body =
  {uses : string; sims : string; sims_param_ids :  string list;
   body :  state_tyd IdMap.t}

type sim_def_tyd = sim_body located

type typed_spec =
  { direct_ios       : io_tyd IdMap.t;
    adversarial_ios  : io_tyd IdMap.t;
    functionalities  : fun_tyd IdMap.t;
    simulators       : sim_def_tyd IdMap.t;
  }

open UcTypedSpec

(* params_map_to_list converts ty_index IdMap.t into a list of
name, type pairs. The list is ordered according to the index of ty_index *)
let params_map_to_list (pm : ty_index IdMap.t) : (string * EcTypes.ty) list =
  let bpm = IdMap.bindings pm in
  let bpm = List.map (fun (s,ti) -> (s, EcLocation.unloc ti)) bpm in
  let bpm_ord = List.sort (fun (_,(_,i1)) (_,(_,i2)) -> i1-i2) bpm in
  List.map (fun (name,(ty,_)) -> (name, ty)) bpm_ord

let mid2IdMap (mi : 'a Mid.t) : ('a IdMap.t) =
  Mid.fold (fun ident el im -> IdMap.add (EcIdent.name ident) el im) mi IdMap.empty 

let sparams_map_to_list (pm : ty_index Mid.t) : (string * EcTypes.ty) list =
  params_map_to_list (mid2IdMap pm)

let pp_type (sc : EcScope.scope) (ppf : Format.formatter) (ty : EcTypes.ty)
    : unit =
  let ppe = EcPrinting.PPEnv.ofenv (EcScope.env sc) in
  EcPrinting.pp_type ppe ppf ty

let open_theory (name : string) : string = "theory "^name^"."

let close_theory (name : string) : string = "end "^name^"."

let uc_name (name : string) : string = "UC_"^name

let epdp_op_name (name : string) : string = "epdp_"^name

let msg_ty_name (name : string) : string = "_"^name

let name_record (msg_name : string) (param_name : string) : string = msg_name^"__"^param_name

let name_record_dir_port (name : string)  (mb : message_body_tyd) : string =
  name_record name (EcUtils.oget mb.port)

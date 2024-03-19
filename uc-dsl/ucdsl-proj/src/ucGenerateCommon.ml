open UcTypedSpec
open UcSpecTypedSpecCommon

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

module SLMap = Map.Make(SL)

let make_msg_path_map (maps : maps_tyd)
: message_body_tyd SLMap.t =
  let make_map (itmap : inter_tyd IdPairMap.t) : message_body_tyd SLMap.t =
    let add_mbs
          (slmap : message_body_tyd SLMap.t)
          (pfx : string list)
          (bibt : basic_inter_body_tyd) :  message_body_tyd SLMap.t =
      IdMap.fold (fun id mb slmap ->
          SLMap.add (pfx@[id]) mb slmap
        ) bibt slmap
    in
    IdPairMap.fold (fun idpair it slmap ->
        let root = fst (idpair) in
        let sl = [root ; snd (idpair)] in
        match (EcLocation.unloc it) with
        | BasicTyd bt -> add_mbs slmap sl bt
        | CompositeTyd ct -> IdMap.fold (fun id bid slmap ->
                                 let it = get_inter_tyd maps root bid in
                                 let ibt = EcLocation.unloc (EcUtils.oget it) in
                                 let bt = basic_tyd_of_inter_body_tyd ibt in
                                 let sl = sl @ [id] in
                                 add_mbs slmap sl bt
                               ) ct slmap
      ) itmap SLMap.empty
  in
  let dirmap = make_map maps.dir_inter_map in
  let advmap = make_map maps.adv_inter_map in
  SLMap.union (fun _ _ _ -> UcMessage.failure "union of SLmaps fail")
    dirmap advmap

let get_msg_body
(mbmap : message_body_tyd SLMap.t) (root : string) (mpp : msg_path_pat)
    : message_body_tyd =
  let mpp = EcLocation.unloc mpp in
  let msgnm =
    match mpp.msg_or_star with
    | MsgOrStarMsg s -> s
    | MsgOrStarStar -> UcMessage.failure "impossible should be Msg"
  in
  let sl = [root]@mpp.inter_id_path@[msgnm] in
  SLMap.find sl mbmap

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

let _self = "_self"
let _adv = "_adv"

let open_theory (name : string) : string = "theory "^name^"."

let close_theory (name : string) : string = "end "^name^"."

let uc_name (name : string) : string = "UC_"^name

let uc__name (name : string) : string = "UC__"^name

let adv_if_pi_op_name = "_adv_if_pi"

let adv_if_pi_gt0_axiom_name = "_adv_if_pi_gt0"

let adv_pi_begin_op_name = "_adv_pi_begin"

let adv_pi_begin_gt0_axiom_name = "_adv_pi_begin_gt0"

let adv_pi_num_op_name = "_adv_pi_num"

let self = "self"

let addr_op_name (name : string) : string = "_addr_"^name

let addr_op_call (name : string) : string = "_addr_"^name^" "^_self

let extport_op_name (name : string) : string = "_extport_"^name

let extport_op_call (name : string) : string = "_extport_"^name^" "^_self

let intport_op_name (name : string) : string = "_intport_"^name

let intport_op_call (name : string) : string = "_intport_"^name^" "^_self

let adv_pt_pi_op_name (name : string) : string = "_adv_pt_pi_"^name

let adv_sf_pi_op_name (name : string) : string = "_adv_pt_pi_"^name

let epdp_op_name (name : string) : string = "epdp_"^name

let msg_ty_name (name : string) : string = "_"^name

let name_record_func (msg_name : string) : string = msg_name^"___func"

let name_record_adv (msg_name : string) : string = msg_name^"___adv"

let name_record (msg_name : string) (param_name : string) : string = msg_name^"__"^param_name

let name_record_dir_port (name : string)  (mb : message_body_tyd) : string =
  name_record name (EcUtils.oget mb.port)

let mode_Dir : string = "Dir"

let mode_Adv : string = "Adv"

let pp_expr ?(ptnms : string list  = []) (sc : EcScope.scope) 
(ppf : Format.formatter) (expr : EcTypes.expr)
    : unit =
  let addr_ex_of_idstr (idstr : string) =
    EcTypes.e_local (EcIdent.create idstr) addr_ty
  in
  let e_self = addr_ex_of_idstr _self in
  
  (* envport substitution *)
  let envport_self =
    EcTypes.e_app envport_op [e_self]
      (EcTypes.tfun port_ty EcTypes.tbool) in
  let envport_subst =
    EcSubst.add_elocals EcSubst.empty [envport_id] [envport_self] in
  let expr = EcSubst.subst_expr envport_subst expr in
  
  (* intport substitution *)
  let intport_op_ex ptnm : EcTypes.expr =
    EcTypes.e_op (EcPath.fromqsymbol ([], intport_op_name ptnm)) []
      (EcTypes.tfun addr_ty port_ty)
  in
  let intport_self ptnm =
    EcTypes.e_app (intport_op_ex ptnm) [e_self] port_ty in
  let expr = List.fold_left (fun ex ptnm ->
    let id = EcIdent.create ("intport:" ^ ptnm) in
    print_endline (EcIdent.tostring id);             
    let intport_subst =
      EcSubst.add_elocals
        EcSubst.empty [id] [intport_self ptnm] in
      EcSubst.subst_expr intport_subst ex
    ) expr ptnms in
  let ppe = EcPrinting.PPEnv.ofenv (EcScope.env sc) in
  EcPrinting.pp_expr ppe ppf expr



let clone_singleton_unit
(ppf : Format.formatter) (root : string) (asname : string) (advpi : string) =
  Format.fprintf ppf "@[<v>";
  Format.fprintf ppf  "@[clone %s as %s with  (* singleton unit *)@]@;"
    (uc_name root) asname;
  Format.fprintf ppf "@[op %s <- %s@]@;"
    adv_if_pi_op_name advpi;
  Format.fprintf ppf "@[proof *.@]@;";
  Format.fprintf ppf "@[realize %s. smt(%s). qed.@]@;@;"
    adv_if_pi_gt0_axiom_name adv_pi_begin_gt0_axiom_name;
  Format.fprintf ppf "@]@;"

let clone_triple_unit
(ppf : Format.formatter) (root : string) (asname : string) (advpibeg : string) =
  Format.fprintf ppf "@[<v>";
  Format.fprintf ppf  "@[clone %s as %s with  (* triple unit *)@]@;"
    (uc_name root) asname;
  Format.fprintf ppf "@[op %s <- %s@]@;"
    adv_pi_begin_op_name advpibeg;
  Format.fprintf ppf "@[proof *.@]@;";
  Format.fprintf ppf "@[realize %s. smt(%s). qed.@]@;@;"
    adv_pi_begin_gt0_axiom_name adv_pi_begin_gt0_axiom_name;
  Format.fprintf ppf "@]@;"

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

let get_msg_path (mpp : msg_path_pat) : msg_path =
  let mppu = EcLocation.unloc mpp in
  let msgn =
    match mppu.msg_or_star with
    | MsgOrStarMsg s -> s
    | MsgOrStarStar -> UcMessage.failure "impossible should be Msg"
  in
  EcLocation.mk_loc (EcLocation.loc mpp)
  {
    inter_id_path = mppu.inter_id_path;
    msg = msgn
  }

(*returns a bool that determines if the interface path is a local path (true),
  or references an interface defined in another file (false)
  together with message body*)
let get_msg_body
      (mbmap : message_body_tyd SLMap.t) (root : string)
      (iip : string list) (msgnm : string)
    : (bool * message_body_tyd) =
  let sl = iip@[msgnm] in
  if SLMap.exists (fun p _ -> p = sl) mbmap
  then let mb = SLMap.find sl mbmap in (false,mb)
  else let mb = SLMap.find ([root]@sl) mbmap in (true,mb)

type rf_addr_port_maps =
  {
    params_addr_sufix : int IdMap.t;
    subfun_addr_sufix : int IdMap.t;
    party_ext_port_id : int IdMap.t;
    party_int_port_id : int IdMap.t;
  }

let make_rf_addr_port_maps (maps : maps_tyd) (root : string) (ft : fun_tyd)
    : rf_addr_port_maps =
  let rfbt = real_fun_body_tyd_of (EcLocation.unloc ft) in
  let pas = IdMap.mapi ( fun nm _ ->
    fst (EcUtils.oget
    (get_child_index_and_comp_inter_sp_of_param_or_sub_fun_of_real_fun
    maps root ft nm))
    ) rfbt.params in
  let sas = IdMap.mapi ( fun nm _ ->
    fst (EcUtils.oget
    (get_child_index_and_comp_inter_sp_of_param_or_sub_fun_of_real_fun
    maps root ft nm))
              ) rfbt.sub_funs in
  let rfinfo = get_info_of_real_func maps root 0 ft in
  let pepi = IdMap.mapi ( fun nm pi ->
                         let _,_, port = EcUtils.oget pi.pi_pdi in
                         port
               ) rfinfo in
  let pipi = IdMap.mapi ( fun nm pi ->
    pi.pi_ipi
               ) rfinfo in
  {
    params_addr_sufix = pas;
    subfun_addr_sufix = sas;
    party_ext_port_id = pepi;
    party_int_port_id = pipi;
  }

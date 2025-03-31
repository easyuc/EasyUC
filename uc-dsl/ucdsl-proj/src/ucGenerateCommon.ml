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
  Mid.fold (fun ident el im -> IdMap.add (EcIdent.name ident) el im)
    mi IdMap.empty 

let sparams_map_to_list (pm : ty_index Mid.t) : (string * EcTypes.ty) list =
  params_map_to_list (mid2IdMap pm)

let pp_type (sc : EcScope.scope) (ppf : Format.formatter) (ty : EcTypes.ty)
    : unit =
  let ppe = EcPrinting.PPEnv.ofenv (EcScope.env sc) in
  EcPrinting.pp_type ppe ppf ty

let pp_form (sc : EcScope.scope) (ppf : Format.formatter) (form : EcFol.form)
    : unit =
  let ppe = EcPrinting.PPEnv.ofenv (EcScope.env sc) in
  EcPrinting.pp_form ppe ppf form

let _self = "_self"

let _st = "_st"

let st_name (name : string) = "_st_"^name

let adv = "adv"

let _pi = "pi"

let open_theory (name : string) : string = "theory "^name^"."

let open_abstract_theory (name : string) : string = "abstract theory "^name^"."

let close_theory (name : string) : string = "end "^name^"."

let uc_name (name : string) : string = "UC_"^name

let bi_name (id : string) : string = (uc_name id)^"_abs"

let uc__name (name : string) : string = "UC__"^name

let rest_name (name : string) (idx : int) : string =
  (uc_name name)^"_Rest"^(string_of_int idx)

let adv_if_pi_op_name = "_adv_if_pi"

let adv_if_pi_gt0_axiom_name = "_adv_if_pi_gt0"

let adv_pi_begin_op_name = "_adv_pi_begin"

let adv_pi_begin_param pmn = "_adv_pi_begin_"^(uc_name pmn)

let adv_pi_begin_gt0_axiom_name = "_adv_pi_begin_gt0"

let adv_pi_num_op_name = "_adv_pi_num"

let self = "self"

let addr_op_name (name : string) : string = "_addr_"^name

let addr_op_call ?(pfx = "") (name : string) : string
  = (addr_op_name name)^" "^pfx^_self

let extport_op_name (name : string) : string = "_extport_"^name

let extport_op_call  ?(pfx = "") (name : string) : string =
  "_extport_"^name^" "^pfx^_self

let intport_op_name (name : string) : string = "_intport_"^name

let intport_op_call ?(pfx = "") (name : string) : string =
  "_intport_"^name^" "^pfx^_self

let adv_pt_pi_op_name (name : string) : string = "_adv_pt_pi_"^name

let epdp_op_name (name : string) : string = "epdp_"^name

let msg_ty_name (name : string) : string = "_"^name

let name_record_func (msg_name : string) : string = msg_name^"___func"

let name_record_adv (msg_name : string) : string = msg_name^"___adv"

let name_record (msg_name : string) (param_name : string) : string = msg_name^"__"^param_name

let name_record_dir_port (name : string)  (mb : message_body_tyd) : string =
  name_record name (EcUtils.oget mb.port)

let mode_Dir : string = "Dir"

let mode_Adv : string = "Adv"

let _Adv : string = "Adv"

let if_addr_opt = "if_addr_opt"

let oget_if_addr_opt = "(oget "^if_addr_opt^")"

let rf_info = "rf_info"

let rest_composition_clone (rest_idx : int) =
  (uc__name "Rest")^(string_of_int rest_idx)

let rest_nameP (id : string) (rfbt : real_fun_body_tyd) (i : int) =
  if IdMap.cardinal rfbt.params <= 1
  then rest_name id i
  else (rest_name id i)^"_P"

let _RFRP = "RFRP"
let _IF = "IF"
let _COMPENV = "COMPENV"
let compenv (i : int) = _COMPENV^(string_of_int i)
let uc_metric_name = "_metric"
let _invar = "_invar"
let _metric_good = "_metric_good"
let uc_metric_name_IF = "_metric_IF"
let uc_metric_RP = "_metric_RP"
let uc_metric_IP = "_metric_IP"
let makeRF_init_invar_lemma (makeRF_module : string) = makeRF_module^"_init"
let makeRF_invoke_lemma (makeRF_module : string) = makeRF_module^"_invoke"
let makeRF_invar_op (makeRF_module : string) =_invar^"_"^ makeRF_module
let makeRF_metric_op (makeRF_module : string) =
  uc_metric_name^"_"^ makeRF_module
let makeRF_metric_good_lemma (makeRF_module : string) =
  makeRF_module^_metric_good
let _metric_RFRP = makeRF_metric_op _RFRP
let _metric_IF = "_metric_IF"
let rest_metric i = "_metric_Rest"^(string_of_int i)
let uc_party_metric_name pn = "_metric_"^pn
let glob_op_name top_mod sub_mod =  "glob_"^top_mod^"_to_"^sub_mod
let glob_op_name_own top_mod = glob_op_name top_mod "own"
let glob_to_part_op_name module_name part_name =
  "glob_"^module_name^"_to_"^part_name
let module_name_IF name = (uc_name name)^"."^_IF
let module_name_RF name = (uc_name name)^"."^_RFRP
let invoke = "invoke"
let _invoke = "_invoke"
let _invoke_pn pn = "_invoke_"^pn
let _invoke_pn_rest pn rest_idx =
  "_invoke_"^pn^"_Rest"^(string_of_int rest_idx)
let iF_invoke = "IF_invoke"
let rFRP_invoke =  makeRF_invoke_lemma _RFRP
let _invoke_IP = "_invoke_IP"
let _invoke_RP = "_invoke_RP"
let rest_invoke i = "_invoke_Rest"^(string_of_int i)
let _invar_IP = "_invar_IP"
let _invar_RP = "_invar_RP"
let rest_invar i = "_invar_Rest"^(string_of_int i)
let invar_pt_op_name ptn = "_invar_"^ptn
let _invar_IF = "_invar_IF"
let _invar_RFRP = makeRF_invar_op _RFRP
let rest_metric_good i = "_metric_good_Rest"^(string_of_int i)
let rFRP_metric_good = makeRF_metric_good_lemma _RFRP
let iF_metric_good = "IF_metric_good"
let _metric_good_RP = "_metric_good_RP"
let _metric_good_IP = "_metric_good_IP"
let init = "init"
let _init = "_init"
let rFRP_init = makeRF_init_invar_lemma _RFRP
let iF_init = "IF_init"
let _init_RP = "_init_RP"
let _init_IP = "_init_IP"
let rest_init i = "_init_Rest"^(string_of_int i)
let simcomp = "SIMCOMP"


let module_name (id : string) = uc_name id
    
let moduleRP (id : string) (rfbt : real_fun_body_tyd) =
  if IdMap.is_empty rfbt.params
  then (module_name id)
  else (module_name id) ^ "_RP"

let metricRP (rfbt : real_fun_body_tyd) =
  if IdMap.is_empty rfbt.params
  then uc_metric_name
  else uc_metric_RP

let metric_goodRP (rfbt : real_fun_body_tyd) =
  if IdMap.is_empty rfbt.params
  then _metric_good
  else _metric_good_RP

let invarRP (rfbt : real_fun_body_tyd) =
  if IdMap.is_empty rfbt.params
  then _invar
  else _invar_RP

let invokeRP (rfbt : real_fun_body_tyd) =
  if IdMap.is_empty rfbt.params
  then _invoke
  else _invoke_RP

let initRP (rfbt : real_fun_body_tyd) =
  if IdMap.is_empty rfbt.params
  then _init
  else _init_RP

let moduleIP (id : string) = (module_name id) ^ "_IP"
  
let moduleIRP (id : string) (rfbt : real_fun_body_tyd)
      (real_params : bool) (rest_idx : int option) =
  match rest_idx with
  | None -> if real_params
            then moduleRP id rfbt
            else moduleIP id
  | Some i -> rest_nameP id rfbt i
  
let module_name_IRF (rfbt : real_fun_body_tyd) (real_params : bool)
      (rest_idx : int option) (param_idx : int) =
  match rest_idx with
  | None -> if real_params
            then module_name_RF
            else module_name_IF
  | Some i -> if param_idx+1 < i
              then module_name_IF
              else module_name_RF

let metricIRF (rfbt : real_fun_body_tyd) (real_params : bool)
      (rest_idx : int option) (param_idx : int) =
  match rest_idx with
  | None -> if real_params
            then _metric_RFRP
            else _metric_IF
  | Some i -> if param_idx+1 < i
              then _metric_IF
              else _metric_RFRP

let metric_name_IRP (rfbt : real_fun_body_tyd) (real_params : bool)
  (rest_idx : int option) =
  match rest_idx with
  | None -> if real_params
            then metricRP rfbt
            else uc_metric_IP
  | Some i -> rest_metric i

let invokeIRF (rfbt : real_fun_body_tyd) (real_params : bool)
      (rest_idx : int option) (param_idx : int) =
  match rest_idx with
  | None -> if real_params
            then rFRP_invoke
            else iF_invoke
  | Some i -> if param_idx+1 < i
              then iF_invoke
              else rFRP_invoke


let invarIRF (rfbt : real_fun_body_tyd) (real_params : bool)
      (rest_idx : int option) (param_idx : int) =
  match rest_idx with
  | None -> if real_params
            then _invar_RFRP
            else _invar_IF
  | Some i -> if param_idx+1 < i
              then _invar_IF
              else _invar_RFRP

let invokeIRP (rfbt : real_fun_body_tyd) (real_params : bool)
  (rest_idx : int option) =
  match rest_idx with
  | None -> if real_params
            then invokeRP rfbt
            else _invoke_IP
  | Some i -> rest_invoke i

let invarIRP (rfbt : real_fun_body_tyd) (real_params : bool)
(rest_idx : int option) =
  match rest_idx with
  | None -> if real_params
            then invarRP rfbt
            else _invar_IP
  | Some i -> rest_invar i 

let initIRP (rfbt : real_fun_body_tyd) (real_params : bool)
  (rest_idx : int option) =
  match rest_idx with
  | None -> if real_params
            then initRP rfbt
            else _init_IP
  | Some i -> rest_init i

let initIRF (rfbt : real_fun_body_tyd) (real_params : bool)
      (rest_idx : int option) (param_idx : int) =
  match rest_idx with
  | None -> if real_params
            then rFRP_init
            else iF_init
  | Some i -> if param_idx+1 < i
              then iF_init
              else rFRP_init

let metric_goodIRP (rfbt : real_fun_body_tyd) (real_params : bool)
  (rest_idx : int option) =
  match rest_idx with
  | None -> if real_params
            then metric_goodRP rfbt
            else _metric_good_IP
  | Some i -> rest_metric_good i

let metric_goodIRF(rfbt : real_fun_body_tyd) (real_params : bool)
      (rest_idx : int option) (param_idx : int) =
  match rest_idx with
  | None -> if real_params
            then rFRP_metric_good
            else iF_metric_good
  | Some i -> if param_idx+1 < i
              then iF_metric_good
              else rFRP_metric_good

let parametrized_rest_module (id : string) (rfbt : real_fun_body_tyd) (i : int)
  = moduleIRP id rfbt true (Some i)

let pp_form ?(is_sim:bool=false) ?(intprts : EcIdent.t QidMap.t = QidMap.empty)
      ?(glob_pfx = "") (sc : EcScope.scope) (ppf : Format.formatter)
      (form : EcFol.form) : unit =
  let addr_ex_of_idstr (idstr : string) =
    EcFol.f_local (EcIdent.create idstr) addr_ty
  in

  let f_self = addr_ex_of_idstr (glob_pfx^_self) in
  
  (* envport substitution *)
  let envport_self =
    EcFol.f_app envport_op [f_self]
      (EcTypes.tfun port_ty EcTypes.tbool) in
  let envport_subst =
    EcSubst.add_flocal EcSubst.empty envport_id envport_self in
  let form = EcSubst.subst_form envport_subst form in

  let f_oget_if_addr_opt =
    let f_if_addr_opt =
      EcFol.f_local (EcIdent.create if_addr_opt) (EcTypes.toption addr_ty) in
    let f_oget (f : EcFol.form) (ty : EcTypes.ty) : EcFol.form =
      let op = EcFol.f_op EcCoreLib.CI_Option.p_oget [ty]
                 (EcTypes.tfun (EcTypes.toption ty) ty)
      in
      EcFol.f_app op [f] ty
    in
    f_oget f_if_addr_opt addr_ty in
  
  (* intport substitution *)
  let intport_op_ex (ptnm : string list) : EcFol.form =
    let ptnm = List.nth ptnm ((List.length ptnm)-1) in
    EcFol.f_op (EcPath.fromqsymbol ([], intport_op_name ptnm)) []
      (EcTypes.tfun addr_ty port_ty)
  in
  let intport_self ptnm =
    let addr_ex = if is_sim then f_oget_if_addr_opt else f_self in
    EcFol.f_app (intport_op_ex ptnm) [addr_ex] port_ty in
  let form = QidMap.fold (fun ptnm id ex  ->        
    let intport_subst =
      EcSubst.add_flocal
        EcSubst.empty id (intport_self ptnm) in
      EcSubst.subst_form intport_subst ex
    ) intprts form in
  let ppe = EcPrinting.PPEnv.ofenv (EcScope.env sc) in
  EcPrinting.pp_form ppe ppf form



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
    party_ext_port_id : int option  IdMap.t;
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
  let pepi = IdMap.mapi ( fun nm pi : int option->
                          if pi.pi_pdi <> None
                          then
                            let _,_, port = EcUtils.oget pi.pi_pdi in
                            Some port
                          else
                            None
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

let get_msg_info (mp : msg_path) (dii : symb_pair IdMap.t)
      (ais : symb_pair IdPairMap.t) (root : string)
      (mbmap : message_body_tyd SLMap.t)
    : string * bool * string * string * message_body_tyd * string =
  
  let qual_epdp_name (msgn : string) (pfx : string)
      : string =
    let _mty_name = msg_ty_name msgn in
    let _epdp_op_name = epdp_op_name _mty_name in
    pfx^_epdp_op_name
  in

  let inter_id_path_str (loc : bool) (iip : string list) : string =
    let iip =
      if loc
      then
        let th = List.hd iip in [uc_name th]@(List.tl iip)
      else
        let fl,th,tl = List.hd iip, List.hd (List.tl iip), List.tl (List.tl iip)
        in [uc_name fl]@[uc_name th]@tl
    in    
    List.fold_left (fun n p -> n^p^".") "" iip
  in
  
    let msg_path = EcLocation.unloc mp in
    let msgn = msg_path.msg in
    let iiphd = List.hd msg_path.inter_id_path in
    let is_internal = IdMap.mem iiphd dii in
    let sim_key iip =  (iiphd, List.hd (List.tl iip)) in
    let is_simulated = ((List.length msg_path.inter_id_path)>1) &&
      IdPairMap.mem (sim_key msg_path.inter_id_path) ais in
    let pfx, mb =
      if is_internal
      then
        let root, int_id = IdMap.find iiphd dii in
        let iiptl = List.tl msg_path.inter_id_path in
        let iip = [root]@[int_id]@iiptl in
        let _,mb = get_msg_body mbmap root iip msgn in
        let pfx = inter_id_path_str true (List.tl iip) in
        let pfx = (uc_name iiphd)^"."^pfx in
        pfx, mb
      else
        if is_simulated
        then
          let key = sim_key msg_path.inter_id_path in
          let root, int_id = IdPairMap.find key ais in
          let iiptl = List.tl (List.tl msg_path.inter_id_path) in
          let is_party_interface = int_id = snd key in
          let iip =
            if is_party_interface
            then [root]@[int_id]@iiptl (* simulating interface of a party*)
            else [root]@iiptl (* simulating interface of a sub functionality or parameter*)    
          in
          let _,mb = get_msg_body mbmap root iip msgn in
          let pfx = inter_id_path_str true (List.tl iip) in
          if is_party_interface
          then
            pfx, mb
          else
            let pfx = (uc_name (snd key))^"."^pfx in
            pfx, mb
        else   
          let iip = msg_path.inter_id_path in
          let loc,mb = get_msg_body mbmap root iip msgn in
          let pfx = inter_id_path_str loc iip in
          pfx, mb
    in
    let epdp_str = qual_epdp_name msgn pfx in
    msgn, is_internal, iiphd, pfx, mb, epdp_str


let linearize_state_DAG (states : state_tyd IdMap.t) : int IdMap.t option =
  let initial_state_id : string = initial_state_id_of_states states in
  let rec add_next_level_states (sls : IdSet.t list) : IdSet.t list option =
    let last = List.hd sls in
    let prev = List.fold_left (fun ret set -> IdSet.union ret set) IdSet.empty sls in
    let next_sl = IdSet.fold (fun st_id idseto ->
                      match idseto with
                      | None -> None 
                      | Some idset ->
                         let s = IdMap.find st_id states in
                         let ns = state_transitions_of_state s in
                         if IdSet.exists (fun id ->
                                IdSet.mem id prev
                              ) ns
                         then None
                         else Some (IdSet.union idset ns)
                    ) last (Some IdSet.empty) in
    match next_sl with
    | None -> None
    | Some sl -> if IdSet.is_empty sl
                 then Some sls
                 else add_next_level_states (sl::sls)
  in
  let init = [IdSet.singleton initial_state_id] in
  let lvls = add_next_level_states init in
  match lvls with
  | None -> None  
  | Some sls -> let _, lin =
                  List.fold_left (fun (lvl_no,lin) sl ->
                    let lin = IdSet.fold (fun id lin ->
                                  IdMap.add id lvl_no lin
                                ) sl lin in
                    (lvl_no + 1, lin)
                    ) (0,IdMap.empty) sls in
                Some lin

let get_own_glob_size_map (ftm : fun_tyd IdPairMap.t) : int IdPairMap.t =
  let ogs (ft : fun_tyd) : int =
    match EcLocation.unloc ft with
    | FunBodyRealTyd rfbt ->
       1 + (IdMap.cardinal rfbt.sub_funs)*2 + (IdMap.cardinal rfbt.parties) 
    | FunBodyIdealTyd _ -> 2
  in
  IdPairMap.map (fun ft -> ogs ft) ftm

type pSP = IF of SP.t | RF of (SP.t * (pSP list)) | Dropped

let getSP (psp : pSP) : SP.t =
  match psp with
  | IF sp -> sp
  | RF (sp, _) -> sp
  | Dropped -> UcMessage.failure "No identifier for dropped parameter"

(*the param_idx determines which parameter will be dropped out,
  all the parameters with smaller index are ideal funcs,
  all the parameters with larger index are real funcs with real params.
 Fully real functionality is obtained by setting param_idx = 0*)
let rec make_pSP (mt : maps_tyd) (funcId : SP.t) (param_idx : int): pSP =
  let ft = IdPairMap.find funcId mt.fun_map in
  let fbt = EcLocation.unloc ft in
  if (is_ideal_fun_body_tyd fbt)
  then IF funcId
  else
    let np = num_params_of_real_fun_tyd ft in
    let get_nth_param_id n =
      let pname = param_name_nth_of_real_fun_tyd ft n in
      let r,_ = id_dir_inter_of_param_of_real_fun_tyd ft pname in
      let rui = unit_info_of_root mt r in
      match rui with
      | UI_Singleton si -> (si.si_root, si.si_ideal)
      | UI_Triple ti -> if n+1 > param_idx
                        then (ti.ti_root, ti.ti_real)
                        else (ti.ti_root, ti.ti_ideal)
    in
    let paramIds = List.init np (fun n -> get_nth_param_id n) in
    let ppSP = List.mapi (fun i fid ->
                   if i+1 = param_idx
                   then Dropped
                   else make_pSP mt fid 0 ) paramIds in
    RF (funcId, ppSP)

type globVarId = string list * string

let compare_globVarIds (g1 : globVarId) (g2 : globVarId) : int =
  let l1 = List.length (fst g1) in
  let l2 = List.length (fst g2) in
  if l1 = l2
  then
    compare g1 g2
  else l1 - l2


let get_subfun_path (thpath : string list) (sfname : string) (rootid : string) =
  thpath @ [uc_name sfname] @ [uc_name rootid]

let get_IF_globVarIds (funpath : string list) : globVarId list =
  [
    (funpath, _self);
    (funpath, _st)
  ]

let get_subfun_globVarIds
(thpath : string list) (sfname : string) (rootid : string) : globVarId list =
  let funpath = get_subfun_path thpath sfname rootid in
  get_IF_globVarIds funpath

let get_party_globVarId (funpath : string list) (ptname : string) : globVarId =
  (funpath, (st_name ptname))

let get_self_globVarId (funpath : string list) : globVarId =
  (funpath, _self)

let get_MakeRF_self_globVarId  (thpath : string list) : globVarId  =
  (thpath @ ["RFCore"] @ ["MakeRF"], "self")
  
let rec get_globVarIds
(mt : maps_tyd) (psp : pSP) (thpath : string list) (funsufix : string list)
        : globVarId list =
  let funpath : string list = thpath @ funsufix in
  let fbt = (EcLocation.unloc (IdPairMap.find (getSP psp) mt.fun_map)) in
  let gvil = 
  match psp with
  | RF (_ , params) ->
    let rfbt = real_fun_body_tyd_of fbt in
    let subfunglobs = IdMap.mapi (fun id ( _ , rid) ->
                          get_subfun_globVarIds thpath id rid) rfbt.sub_funs in
    let subfunglobs = List.flatten
                        (snd (List.split (IdMap.bindings subfunglobs))) in
    let partyglobs = IdMap.mapi (fun id _ ->
                         get_party_globVarId funpath id) rfbt.parties in
    let partyglobs = snd (List.split(IdMap.bindings partyglobs)) in
    let ownglobs = [get_self_globVarId funpath] @ partyglobs @ subfunglobs in
    let param_names = fst (List.split (indexed_map_to_list_keep_keys
                                         rfbt.params)) in
    let paraml = List.combine param_names params in
    let paraml = List.filter (fun (id, psp) -> psp <> Dropped) paraml in
    let paramglobs = List.map (fun (id, psp) ->
                         let thpath = thpath @ [uc_name id] in
                         let funsufix = [uc_name (fst(getSP psp))] in
                         let globs = get_globVarIds mt psp thpath funsufix in
                         match psp with
                           | IF _ -> globs
                           | RF _ ->
                              let makeRFself=get_MakeRF_self_globVarId thpath in
                              makeRFself :: globs
                           | Dropped -> UcMessage.failure
                                          "impossible dropped param"
                       ) paraml
    in
    let paramglobs = List.flatten paramglobs in
    ownglobs @ paramglobs
  | IF _ -> get_IF_globVarIds funpath
  | Dropped -> UcMessage.failure
                 "get_globVarIds cannot be called for dropped parameter of Rest" 
  in
  List.sort compare_globVarIds gvil
  
let get_globVarIds_of_fully_real_fun_glob_core
      (mt : maps_tyd) (funcId : SP.t) : globVarId list =
  let psp = make_pSP mt funcId 0 in
  get_globVarIds mt psp [] [uc_name (snd funcId)]

let get_param_num (mt : maps_tyd) (funcId : SP.t) : int =
  let ft = IdPairMap.find funcId mt.fun_map in
  num_params_of_real_fun_tyd ft

let get_globVarIds_of_real_fun_w_ideal_params_glob_core
      (mt : maps_tyd) (funcId : SP.t) : globVarId list =
  let np = get_param_num mt funcId in
  let psp = make_pSP mt funcId (np+1) in
  get_globVarIds mt psp [] [uc_name (snd funcId)]

let get_globVarIds_of_Rest_modules
      (mt : maps_tyd) (funcId : SP.t) : globVarId list list =
  let np = get_param_num mt funcId in
  List.init np (fun n ->
      let idx = n+1 in
      let psp = make_pSP mt funcId idx in
      get_globVarIds mt psp [] [rest_name (snd funcId) idx])

  

type gvil = { gvil_RP : globVarId list;
              gvil_IP : globVarId list;
              gvil_Rest : globVarId list list
            }

let get_gvil (mt : maps_tyd) (funcId : SP.t) : gvil =
  {
    gvil_RP = get_globVarIds_of_fully_real_fun_glob_core mt funcId;
    gvil_IP = get_globVarIds_of_real_fun_w_ideal_params_glob_core mt funcId;
    gvil_Rest = get_globVarIds_of_Rest_modules mt funcId
  }

let empty_gvil = {
    gvil_RP = [];
    gvil_IP = [];
    gvil_Rest = []
  }
                                                    

let get_MakeRFs_glob_range_of_real_fun_glob_core
      (gvil : globVarId list) : int list =
  let coreself = get_MakeRF_self_globVarId [] in
  let gvilc = coreself::gvil  in
  let gvilc = List.sort compare_globVarIds gvilc in
  let ci = EcUtils.oget (List.find_index (fun gvi -> gvi = coreself) gvilc) in
  (*add +1 to index, to increment 0-based indices*)
  let is = List.init (List.length gvilc) (fun i->i+1) in
  List.filter (fun i -> i<>(ci+1)) is

let filter_indices (l : 'a list) (f : 'a -> bool) : int list =
  let indices = List.mapi (fun i a ->
                    if f a
                    then Some i
                    else None
                  ) l in
  
  let indxs = List.filter_map (fun i -> i ) indices in
  (*+1 b.c. first indx in ec is 1, not 0*)
  List.map (fun i -> i+1) indxs

let param_names (rfbt : real_fun_body_tyd) =
  let param_names = fst (List.split (indexed_map_to_list_keep_keys
                                       rfbt.params)) in
  List.map (fun nm -> uc_name nm) param_names

let get_own_glob_range_of_real_fun_glob_core
      (rfbt : real_fun_body_tyd) (gvil : globVarId list) : int list =
  let param_names = param_names rfbt in
  filter_indices gvil (fun gvi ->
      not (List.mem (List.hd(fst gvi)) param_names))

let get_glob_range_of_parameter
      (gvil : globVarId list) (pmn : string): int list =
  filter_indices gvil (fun gvi ->  List.hd(fst gvi) = uc_name pmn)

let get_own_glob_ranges_of_real_fun
      (rfbt : real_fun_body_tyd) (gvil : globVarId list) : int list IdMap.t =
  let param_names = param_names rfbt in
  let owngvil =
    List.filter
      (fun gvi ->
        not(List.mem (List.hd(fst gvi)) param_names)) gvil in
  let subfunmap = IdMap.mapi (fun id _ ->
    filter_indices owngvil (fun gvi -> List.hd(fst gvi) = uc_name id)
      ) rfbt.sub_funs in
  let funcid = List.hd (fst (List.hd owngvil)) in
  let partymap = IdMap.mapi (fun id _ ->
    filter_indices owngvil
      (fun gvi -> List.hd(fst gvi) = funcid
                  && (snd gvi) = (st_name id))
                   ) rfbt.parties in
  IdMap.union (fun _ _ _ ->
      UcMessage.failure "impossible, parties and sub_funs have different names")
    subfunmap partymap

let get_glob_indices_of_real_fun_parties
      (rfbt : real_fun_body_tyd) (gvil : globVarId list) : int IdMap.t =
  let ogrm = get_own_glob_ranges_of_real_fun rfbt gvil in
  IdMap.filter_map (fun id rng ->
      if (IdMap.mem id rfbt.parties)
      then Some (List.hd rng)
      else None ) ogrm

type bound_macro_fun = string -> string -> string -> string

let apply_param_Bound_RFRP_IF_macro_fun (bmf : bound_macro_fun)
      (pmnm : string) (pmno : int) : bound_macro_fun =
  fun s1 s2 s3 ->
  bmf (s1^(uc_name pmnm)^".") (s1^(compenv pmno)^"("^s2^")") s3

let get_RFIP_IF_bound_from_macro (funcId : SP.t) : bound_macro_fun =
  let filename = (fst funcId)^".eca" in
  let macros = UcEasyCryptCommentMacros.scan_and_check_file filename in
  fun s1 s2 s3->
  UcEasyCryptCommentMacros.apply_macro macros "Bound_RFIP_IF" [s1;s2;s3]

let rec get_Bound_RFRP_IF_macro_fun
(mt : maps_tyd) (funcId : SP.t) : bound_macro_fun =
  let fbt = EcLocation.unloc (IdPairMap.find funcId mt.fun_map) in
  let rfbt = real_fun_body_tyd_of fbt in
  let own = get_RFIP_IF_bound_from_macro funcId in
  let paramboundstr = get_params_sum_Bound_RFRP_IF_macro_fun mt funcId in
  fun s1 s2 s3 ->
    if 0 < (IdMap.cardinal rfbt.params)
    then ((paramboundstr s1 s2 s3)^"\n+\n"^(own s1 s2 s3))
    else (own s1 s2 s3)
and get_params_sum_Bound_RFRP_IF_macro_fun
(mt : maps_tyd) (funcId : SP.t) : bound_macro_fun =  
  let fbt = EcLocation.unloc (IdPairMap.find funcId mt.fun_map) in
  let rfbt = real_fun_body_tyd_of fbt in
  let params = indexed_map_to_list_keep_keys rfbt.params in
  if List.length params = 0
  then fun s1 s2 s3 -> ""
  else
    let parambounds : bound_macro_fun list =
      List.mapi (fun i (pmnm, (r,dirint)) ->
        let ui = unit_info_of_root mt r in
        let fid = match ui with
          | UI_Triple ti -> (r,ti.ti_real)
          | _ -> UcMessage.failure
                   "impossible param must be from triple unit" in
        let pbound = get_Bound_RFRP_IF_macro_fun mt fid in
        apply_param_Bound_RFRP_IF_macro_fun pbound pmnm (i+1)) params
    in
    fun s1 s2 s3 ->
      List.fold_left (fun str pbound ->
          (str^"\n+\n"^(pbound s1 s2 s3)))
        ((List.hd parambounds) s1 s2 s3) (List.tl parambounds)
  
let get_Bound_RFRP_IF_macro (mt : maps_tyd) (funcId : SP.t) : string =
  let bmf = get_Bound_RFRP_IF_macro_fun mt funcId in
  let macro_body = bmf "<<ParamName>>" "<<Env>>" "<<Adv>>" in
  "(*! Bound_RFRP_IF(ParamName, Env, Adv)\n"^macro_body^"\n*)"

let get_Bound_RFIP_IF (funcId : SP.t) : string =
   (get_RFIP_IF_bound_from_macro funcId) "" "Env" _Adv

let get_param_Bound_RFRP_IF (rfbt : real_fun_body_tyd) (param_no : int)
    (env : string) (adv : string) : string =
  let params = indexed_map_to_list_keep_keys rfbt.params in
  let (pmnm, funcId) = List.nth params (param_no-1) in
  let filename = (uc_name (fst funcId))^".eca" in
  let macros = UcEasyCryptCommentMacros.scan_and_check_file filename in
  let bmf = fun s1 s2 s3 ->
    UcEasyCryptCommentMacros.apply_macro macros "Bound_RFRP_IF" [s1;s2;s3] in
  let bmf = apply_param_Bound_RFRP_IF_macro_fun bmf pmnm param_no in
  bmf "" env adv

let print_userfile_stub
(fs : out_channel) (root : string) (rf_has_params : bool) =
  let rfip_eq_rfrp =
    if rf_has_params
    then ""
    else "module RFIP = RFRP. (*real fun has no params so real fun with ideal params is the same as real fun with real params*)"
  in
  Printf.fprintf fs
"
require import UCCore.

require UC__%s.

clone include UC__%s.

%s

(*! Bound_RFIP_IF(PathPfx, Env, Adv) 0.0 *)
  
lemma %s_RFIP_IF_advantage
    (Env <: ENV{-MI, -RFIP, -IF, -SIM})
    (Adv <: ADV{-MI, -Env, -RFIP, -IF, -SIM})
    (func' : addr, in_guard' : int fset) &m :
    exper_pre func' =>
    disjoint in_guard' (adv_pis_rf_info rf_info) =>
      (*adv pis of KE are disj. from in_guard'*)    
 `|Pr[Exper(MI(RFIP, Adv), Env)
         .main(func', in_guard')
           @ &m : res] -
    Pr[Exper(MI(IF, SIM(Adv)), Env)
         .main(func', in_guard')
      @ &m : res]| <=
    0.0
      .
proof.
admit.
qed.     
"
root root rfip_eq_rfrp root

let print_UC_file (fs : out_channel) (mt : maps_tyd) (funcId : SP.t) =
  let print_UC_file_func_w_params root paramsumbound boundRFIP_IF =
Printf.fprintf fs
"module %s(Adv : ADV) = SIMIP(SIM(Adv)).
                                                               
lemma %s_RFRP_IF_advantage
    (Env <: ENV{-MI, -RFRP, -AllIFs, -SIMCOMP, -AllCGs})
    (Adv <: ADV{-MI, -Env, -RFRP, -AllIFs, -SIMCOMP, -AllCGs})
    (func' : addr, in_guard' : int fset) &m :
    exper_pre func' =>
    disjoint in_guard' (adv_pis_rf_info rf_info) =>
      
 `|Pr[Exper(MI(RFRP, Adv), Env)
         .main(func', in_guard')
           @ &m : res] -
    Pr[Exper(MI(IF, SIMCOMP(Adv)), Env)
         .main(func', in_guard')
      @ &m : res]| <=
%s
+
%s
.
    proof.
    move => exper disj.
    apply (
    MakeInt.security_trans
    (RFRP)
    (RFIP)
    (IF)
    (Adv)
    (SIMIP(Adv))
    (SIMCOMP(Adv))

    Env
    func' in_guard'
    (
%s
    )
    (%s)
    &m
). 
 by apply (exper_RF_RP_IP_Pr_diff Env Adv func' in_guard' &m).

 by apply (%s_RFIP_IF_advantage Env (SIMIP(Adv)) func' in_guard' &m).
 qed.
 "
simcomp
root
paramsumbound
boundRFIP_IF
paramsumbound
boundRFIP_IF
root
  in
  let print_UC_file_func_wo_params root boundRFIP_IF =
    Printf.fprintf fs
      "module %s(Adv : ADV) = SIM(Adv).

lemma %s_RFRP_IF_advantage
    (Env <: ENV{-MI, -RFRP, -IF, -SIM})
    (Adv <: ADV{-MI, -Env, -RFRP, -IF, -SIM})
    (func' : addr, in_guard' : int fset) &m :
    exper_pre func' =>
    disjoint in_guard' (adv_pis_rf_info rf_info) =>    
 `|Pr[Exper(MI(RFRP, Adv), Env).main(func', in_guard') @ &m : res] -
   Pr[Exper(MI(IF, SIM(Adv)), Env).main(func', in_guard') @ &m : res]|
 <=
 %s
.
    proof.
      apply (%s_RFIP_IF_advantage
      Env
      Adv
      func'
      in_guard'
      &m)
      .
    qed.
 "
simcomp
root
boundRFIP_IF
root
  in
  
  let root = fst funcId in
  let boundmacro = get_Bound_RFRP_IF_macro mt funcId in
  let paramsumbound : string =
    (get_params_sum_Bound_RFRP_IF_macro_fun mt funcId) "" "Env" _Adv in
  let boundRFIP_IF : string = get_Bound_RFIP_IF funcId in
  let has_params =
    let ft = IdPairMap.find funcId mt.fun_map in
    num_params_of_real_fun_tyd ft > 0
  in
  Printf.fprintf fs

"
prover quorum=2 [\"Alt-Ergo\" \"Z3\"].

require import UCCore.

require %s.
                                
clone include %s.

%s
"
  root
  root
  boundmacro
  ;
  if has_params
  then print_UC_file_func_w_params root paramsumbound boundRFIP_IF
  else print_UC_file_func_wo_params root boundRFIP_IF
    
    
  

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

let uc__code = "UC__Code"

let uc__rf = "UC__RF"

let uc__if = "UC__IF"

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

let pp_expr ?(is_sim:bool=false) ?(intprts : EcIdent.t QidMap.t = QidMap.empty)
      ?(glob_pfx = "") (sc : EcScope.scope) (ppf : Format.formatter)
      (expr : EcTypes.expr) : unit =
  let addr_ex_of_idstr (idstr : string) =
    EcTypes.e_local (EcIdent.create idstr) addr_ty
  in

  let e_self = addr_ex_of_idstr (glob_pfx^_self) in
  
  (* envport substitution *)
  let envport_self =
    EcTypes.e_app envport_op [e_self]
      (EcTypes.tfun port_ty EcTypes.tbool) in
  let envport_subst =
    EcSubst.add_elocals EcSubst.empty [envport_id] [envport_self] in
  let expr = EcSubst.subst_expr envport_subst expr in

  let e_oget_if_addr_opt =
    let e_if_addr_opt =
      EcTypes.e_local (EcIdent.create if_addr_opt) (EcTypes.toption addr_ty) in
    EcTypes.e_oget e_if_addr_opt addr_ty in
  
  (* intport substitution *)
  let intport_op_ex (ptnm : string list) : EcTypes.expr =
    let ptnm = List.nth ptnm ((List.length ptnm)-1) in
    EcTypes.e_op (EcPath.fromqsymbol ([], uc__rf^"."^intport_op_name ptnm)) []
      (EcTypes.tfun addr_ty port_ty)
  in
  let intport_self ptnm =
    let addr_ex = if is_sim then e_oget_if_addr_opt else e_self in
    EcTypes.e_app (intport_op_ex ptnm) [addr_ex] port_ty in
  let expr = QidMap.fold (fun ptnm id ex  ->        
    let intport_subst =
      EcSubst.add_elocals
        EcSubst.empty [id] [intport_self ptnm] in
      EcSubst.subst_expr intport_subst ex
    ) intprts expr in
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
  (*List.iter (fun s -> print_string (s^" + ")) sl;
  print_endline "";*)
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
        let pfx = (uc_name iiphd)^"."^uc__code^"."^pfx in
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
            let pfx = (uc_name (snd key))^"."^uc__code^"."^pfx in
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

type pSP = IF of SP.t | RF of (SP.t * (pSP list))

let getSP (psp : pSP) : SP.t =
  match psp with
  | IF sp -> sp
  | RF (sp, _) -> sp

let rec get_glob_size_w_params (ftm : fun_tyd IdPairMap.t) (func : pSP) : int =
  let ogsm = get_own_glob_size_map ftm in
  match func with
  | IF sp -> IdPairMap.find sp ogsm
  | RF (sp, params) ->
     let psize (psp : pSP) : int =
       let is_real  = is_real_fun_body_tyd
                        (EcLocation.unloc (IdPairMap.find (getSP psp) ftm)) in
       (get_glob_size_w_params ftm psp) +
       (*+1 for MakeRF._self*)  
       (if is_real then 1 else 0)
     in
     let own = IdPairMap.find sp ogsm in
     let pms = List.fold_left (fun sum psp -> sum + (psize psp)) 0 params in
     own + pms

let rec make_pSP (mt : maps_tyd) (funcId : SP.t) (real_params : bool): pSP =
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
      | UI_Triple ti -> if real_params
                        then (ti.ti_root, ti.ti_real)
                        else (ti.ti_root, ti.ti_ideal)
    in
    let paramIds = List.init np (fun n -> get_nth_param_id n) in
    RF (funcId, List.map (fun fid -> make_pSP mt fid real_params) paramIds)

type globVarId = string list * string

let compare_globVarIds (g1 : globVarId) (g2 : globVarId) : int =
  let l1 = List.length (fst g1) in
  let l2 = List.length (fst g2) in
  if l1 = l2
  then
    compare g1 g2
  else l1 - l2


let get_subfun_path (thpath : string list) (sfname : string) (rootid : string) =
  thpath @ [uc_name sfname] @ [uc__code] @ [uc__if] @ [uc_name rootid]

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
    let param_names = fst (List.split (IdMap.bindings rfbt.params)) in
    let paraml = List.combine param_names params in
    let paramglobs = List.map (fun (id, psp) ->
                         let thpath = thpath @ [uc_name id] @ [uc__code]in
                         let ifrfth = match psp with
                           | IF _ -> uc__if
                           | RF _ -> uc__rf
                         in
                         let funsufix = [ifrfth] @ [uc_name (fst(getSP psp))] in
                         let globs = get_globVarIds mt psp thpath funsufix in
                         match psp with
                           | IF _ -> globs
                           | RF _ ->
                              let makeRFself=get_MakeRF_self_globVarId thpath in
                              makeRFself :: globs
                       ) paraml
    in
    let paramglobs = List.flatten paramglobs in
    ownglobs @ paramglobs
  | IF _ -> get_IF_globVarIds funpath
  in
  List.sort compare_globVarIds gvil
  
let get_globVarIds_of_fully_real_fun_glob_core
      (mt : maps_tyd) (funcId : SP.t) : globVarId list =
  let psp = make_pSP mt funcId true in
  get_globVarIds mt psp [] [uc_name (snd funcId)]

let get_globVarIds_of_real_fun_w_ideal_params_glob_core
      (mt : maps_tyd) (funcId : SP.t) : globVarId list =
  let psp = make_pSP mt funcId false in
  get_globVarIds mt psp [] [uc_name (snd funcId)]

type gvil = { gvil_RP : globVarId list;
              gvil_IP : globVarId list }

let get_gvil (mt : maps_tyd) (funcId : SP.t) : gvil =
  {
    gvil_RP = get_globVarIds_of_fully_real_fun_glob_core mt funcId;
    gvil_IP = get_globVarIds_of_real_fun_w_ideal_params_glob_core mt funcId
  }

let empty_gvil = {
    gvil_RP = [];
    gvil_IP = []
  }
                                                    

let get_MakeRFs_glob_range_of_real_fun_glob_core
      (gvil : globVarId list) : int list =
  (*add +2, one to increment 0 and another one to make up for MakeRF._self*)
  List.init (List.length gvil) (fun i->i+2)

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
  let param_names = fst (List.split (IdMap.bindings rfbt.params)) in
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
 



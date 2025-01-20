open UcTypedSpec
open UcSpecTypedSpecCommon
open EcTypes
open UcGenerateCommon

let state_name (name : string) : string = "_State_"^name
let state_type_name_IF = "_state"

let state_name_pt (ptname : string) (sname : string) : string =
  "_State_"^ptname^"_"^sname
let state_type_name_pt (ptname : string) : string =
  "_state_"^ptname


let uc__sim = "UC__SIM"
let _RF = "RF"
let _IF = "IF"
let _m = "_m"
let _r = "_r"
let _x = "_x"
let _envport = "envport"
let msg_ty : ty =
  tconstr (EcPath.fromqsymbol (uc_qsym_prefix_basic_types, "msg")) []
let parties_str = "parties"
let loop_str = "loop"
let proc_party_str (pn : string) = "party_"^pn
let if_addr_opt = "if_addr_opt"
let oget_if_addr_opt = "(oget "^if_addr_opt^")"
let addr_op_call_sim (name : string) : string =
  uc__rf^"."^(addr_op_name name)^" "^oget_if_addr_opt
let uc_metric_name = "_metric"
let uc_metric_RP = "_metric_RP"
let uc_metric_IP = "_metric_IP"
let _metric_RF = "_metric_RF"
let _metric_IF = "_metric_IF"
let uc_party_metric_name pn = "_metric_"^pn
let glob_op_name top_mod sub_mod =  "glob_"^top_mod^"_to_"^sub_mod
let glob_op_name_own top_mod = glob_op_name top_mod "own"
let glob_to_part_op_name module_name part_name =
  "glob_"^module_name^"_to_"^part_name
let module_name_IF name = (uc_name name)^"."^_IF
let module_name_RF name = (uc_name name)^"."^_RF
let invoke = "invoke"
let _invoke = "_invoke"
let _invoke_pn pn = "_invoke_"^pn
let _invoke_IF = "_invoke_IF"
let _invoke_RF = "_invoke_RF"
let _invoke_IP = "_invoke_IP"
let _invoke_RP = "_invoke_RP"
let _invar = "_invar"
let _invar_IP = "_invar_IP"
let _invar_RP = "_invar_RP"
let invar_pt_op_name ptn = "_invar_"^ptn
let _invar_IF = "_invar_IF"
let _invar_RF = "_invar_RF"
let _metric_good = "_metric_good"
let _metric_good_RF = "_metric_good_RF"
let _metric_good_IF = "_metric_good_IF"
let _metric_good_RP = "_metric_good_RP"
let _metric_good_IP = "_metric_good_IP"
let _metric_pt_good ptn = "_metric_"^ptn^"_good"
let init = "init"
let _init = "_init"
let _init_RF = "_init_RF"
let _init_IF = "_init_IF"
let _init_RP = "_init_RP"
let _init_IP = "_init_IP"
let module_params_string pmns : string =
  if pmns = []
  then ""
  else
    let hd = List.hd pmns in
    let tl = List.tl pmns in
    (List.fold_left (fun acc pmn -> acc^", "^pmn) ("("^hd) tl)^")"
let _RFRP = "RFRP"
let smt_sat_lemmas = "mem_oflist mem_rangeset"
let rf_info = "rf_info"

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
  
let moduleIRP (id : string) (rfbt : real_fun_body_tyd) (real_params : bool) =
  if real_params
  then moduleRP id rfbt
  else moduleIP id
  
let module_name_IRF (real_params : bool) =
    if real_params
    then module_name_RF
    else module_name_IF

let metricIRF (real_params : bool) =
    if real_params then _metric_RF else _metric_IF

let metric_name_IRP (rfbt : real_fun_body_tyd) (real_params : bool) =
  if real_params
  then metricRP rfbt
  else uc_metric_IP

let invokeIRF (real_params : bool) =
    if real_params then _invoke_RF else _invoke_IF


let invarIRF (real_params : bool) =
  if real_params then _invar_RF else _invar_IF

let invokeIRP (rfbt : real_fun_body_tyd) (real_params : bool) =
  if real_params
  then invokeRP rfbt
  else _invoke_IP

let invarIRP (rfbt : real_fun_body_tyd) (real_params : bool) =
  if real_params
  then invarRP rfbt
  else _invar_IP

let initIRP (rfbt : real_fun_body_tyd) (real_params : bool) =
  if real_params
  then initRP rfbt
  else _init_IP

let initIRF (real_params : bool) =
    if real_params then _init_RF else _init_IF

let metric_goodIRP (rfbt : real_fun_body_tyd) (real_params : bool) =
  if real_params
  then metric_goodRP rfbt
  else _metric_good_IP

let metric_goodIRF (real_params : bool) =
    if real_params then _metric_good_RF else _metric_good_IF

let print_state_type
      (sc : EcScope.scope)
      (ppf : Format.formatter)
      (states : state_tyd IdMap.t)
      (state_type_name : string)
      (state_name : string -> string)
    : unit =
  let s2e (sname, sbod : string * state_tyd) : (string * ty list) =
    let stys = snd (List.split (sparams_map_to_list
    (EcLocation.unloc sbod).params)) in
    ((state_name sname), stys)
  in
  let ste = List.map s2e (IdMap.bindings states) in
  let print_stys ppf stys : unit =
    let sty1 = List.hd stys in
    Format.fprintf ppf "%a" (pp_type sc) sty1;
    List.iter (fun ty -> Format.fprintf ppf "@ &@ %a" (pp_type sc) ty
      ) (List.tl stys)
  in
  Format.fprintf ppf "@[type %s = [ @]@;<0 2>" state_type_name;
  Format.fprintf ppf "@[<v>";
  List.iter (fun (sname, stys) ->
      if List.is_empty stys
      then Format.fprintf ppf "@[| %s@]@;" sname
      else Format.fprintf ppf "@[| %s of %a@]@;" sname print_stys stys
    ) ste;
  Format.fprintf ppf "@]@\n";
  Format.fprintf ppf "].@;"

let print_state_type_IF
      (sc : EcScope.scope)
      (ppf : Format.formatter)
      (states : state_tyd IdMap.t)
    : unit =
  print_state_type sc ppf states state_type_name_IF state_name 

let mmc_proc_name
      (stid : string) (mpp : msg_path_pat) (state_name : string -> string)
    : string =
  let mpp = EcLocation.unloc mpp in
  let stn = state_name stid in
  let msgn = match mpp.msg_or_star with
    | MsgOrStarMsg s -> s
    | MsgOrStarStar -> UcMessage.failure "not possible" in
  (List.fold_left (fun n p -> n^"__"^p) stn mpp.inter_id_path)^"__"^msgn

let mmc_proc_name_IF (stid : string) (mpp : msg_path_pat) : string =
  mmc_proc_name stid mpp state_name
  
let print_proc_params_decl (sc : EcScope.scope) (ppf : Format.formatter)
      (ps : (string * ty) list) : unit =
  let print n t = Format.fprintf ppf ", %s : %a" n (pp_type sc) t
  in
  if List.is_empty ps
  then ()
  else
    let n,t = List.hd ps in
    Format.fprintf ppf "%s : %a" n (pp_type sc) t;
    List.iter (fun (n,t) -> print n t) (List.tl ps)

let print_proc_params_call (ppf : Format.formatter) (ps : string  list) : unit =
  let print n = Format.fprintf ppf ", %s" n
  in
  if List.is_empty ps
  then ()
  else
    let n = List.hd ps in
    Format.fprintf ppf "%s" n;
    List.iter (fun n -> print n) (List.tl ps)
  
let rec print_code (sim_uses : string option)
          (sc :  EcScope.scope) (root : string)
          (mbmap : message_body_tyd SLMap.t)
          (ppf : Format.formatter)
          (code : instruction_tyd list EcLocation.located)
          (state_name : string -> string) (dii : symb_pair IdMap.t)
          (ais : symb_pair IdPairMap.t)
          (ptn : string option)
          (intprts : EcIdent.t QidMap.t)
          (glob_pfx : string): unit =
  let pp_ex = pp_expr ~is_sim:(sim_uses<>None) ~intprts:intprts ~glob_pfx:glob_pfx sc in
(*  let pp_extyargs ppf ex =
    match (EcTypes.e_ty ex).ty_node with
    | EcAst.Tconstr (_,tyargs) ->
       begin match tyargs with
       | [] -> ()
       | hd::tl ->
          begin
          Format.fprintf ppf "<:";
          Format.fprintf ppf "%a" (pp_type sc) hd;
          List.iter (fun ty -> Format.fprintf ppf ", %a" (pp_type sc) ty) tl;
          Format.fprintf ppf ">"
          end
       end
    | _ -> ()
    in
 *)
  let print_fail_instr () : unit =
    Format.fprintf ppf "@[%s <- None;@]" _r
  in
  let print_ite_instr expr thencode elsecodeo : unit =
    Format.fprintf ppf "@[if (%a) {@]@;<0 2>@[<v>" pp_ex expr;
    print_code sim_uses
      sc root mbmap ppf thencode state_name dii ais ptn intprts glob_pfx;
    Format.fprintf ppf  "@]@;}";
    match elsecodeo with
    | Some code ->
      Format.fprintf ppf "@;@[else {@]@;<0 2>@[<v>";
      print_code sim_uses
        sc root mbmap ppf code state_name dii ais ptn intprts glob_pfx; 
      Format.fprintf ppf  "@]@;}"
    | None -> ()
  in
  let print_sat_instr (sat : send_and_transition_tyd) : unit =
    (*send part*)
    let mp = sat.msg_expr.path in
    let msgn, is_internal, iiphd, pfx, mb, epdp_str =
      get_msg_info mp dii ais root mbmap in
    if not is_internal then
    begin match mb.port with
    | Some port ->
       Format.fprintf ppf
         "@[if (%s %s %s) {@]@;<0 2>@[<v>"
         _envport (glob_pfx^_self) port
    | None -> ()
    end
    else ()
    ;
    Format.fprintf ppf "@[%s <- Some@]@;<0 2>@[<v>(%s.`enc@;"
      _r epdp_str;
    Format.fprintf ppf "{|@;<0 2>@[<v>";
    let is_sim = sim_uses <> None in
    let is_sim_to_IF =
      match sim_uses with
      | Some s -> s = iiphd
      | None -> false in
    let sim_from_Party mp : bool =
      let iip = (EcLocation.unloc mp).inter_id_path in
      let sims = List.hd iip in
      let ptnm = List.hd (List.tl iip) in
      let sim_key = (sims,ptnm) in
      is_sim && not is_sim_to_IF &&
        (IdPairMap.mem sim_key ais) && ptnm = snd (IdPairMap.find sim_key ais)
    in
    let sim_from_sf_pm mp : string option =
      let iip = (EcLocation.unloc mp).inter_id_path in
      let sims = List.hd iip in
      let sfpmnm = List.hd (List.tl iip) in
      if IdPairMap.mem (sims,sfpmnm) ais
      then Some sfpmnm
      else None
    in
    if is_sim
    then   
      if is_sim_to_IF
      then
        Format.fprintf ppf "@[%s%s = %s;@]@;"
          pfx (name_record_func msgn) oget_if_addr_opt
      else
        if (sim_from_Party mp)
        then
          Format.fprintf ppf "@[%s%s = %s;@]@;"
          pfx (name_record_func msgn) oget_if_addr_opt
        else
          if (sim_from_sf_pm mp)<> None
          then
            Format.fprintf ppf "@[%s%s = %s;@]@;"
              pfx (name_record_func msgn)
              (addr_op_call_sim (EcUtils.oget (sim_from_sf_pm mp)))
          else
            UcMessage.failure
              "simulator sends only messages to IF or as RF to adv"
    else
      if is_internal
      then
        Format.fprintf ppf "@[%s%s = %s;@]@;"
        pfx (name_record_func msgn) (addr_op_call ~pfx:glob_pfx iiphd)
      else
        Format.fprintf ppf "@[%s%s = %s%s;@]@;"
        pfx (name_record_func msgn) glob_pfx _self
    ;
    begin match mb.port with
    | Some _ ->
       if is_internal
       then
         Format.fprintf ppf "@[%s%s = %s;@]@;"
           pfx (name_record_dir_port msgn mb)
           (intport_op_call ~pfx:glob_pfx (EcUtils.oget ptn))
       else
         Format.fprintf ppf "@[%s%s = %a;@]@;"
           pfx (name_record_dir_port msgn mb) pp_ex
           (EcUtils.oget sat.msg_expr.port_expr)
    | None ->
      Format.fprintf ppf "@[%s%s = %s;@]@;"
        pfx (name_record_adv msgn) adv
    end
    ;
    let pm = fst (List.split (params_map_to_list mb.params_map)) in
    let args = EcLocation.unloc sat.msg_expr.args in 
    List.iteri (fun i pn ->
        Format.fprintf ppf "@[%s%s = %a;@]@;"
        pfx (name_record msgn pn) pp_ex (List.nth args i)
      ) pm;
    Format.fprintf ppf "@]@;|}";
    Format.fprintf ppf ");@]@;";
    (*transition part*)
    let state_var_name =
      match ptn with
      | None -> _st
      | Some pn -> st_name pn in
    Format.fprintf ppf "@[%s%s <- %s"
      glob_pfx state_var_name (state_name (EcLocation.unloc sat.state_expr.id));
    List.iter (fun ex -> Format.fprintf ppf "@ %a"
      pp_ex ex) (EcLocation.unloc sat.state_expr.args);
    Format.fprintf ppf ";@]";
    if not is_internal then
    begin match mb.port with
    | Some port ->
       Format.fprintf ppf "@]@;}"
    | None -> ()
    end
    else ()
  in
  let print_lhs ppf lhs =
      match lhs with
      | LHSSimp ps ->
         Format.fprintf ppf "%s"(EcLocation.unloc ps)
      | LHSTuple psl ->
       begin
         Format.fprintf ppf "(%s" (EcLocation.unloc (List.hd psl));
         List.iter (fun ps ->
             Format.fprintf ppf ", %s" (EcLocation.unloc ps)
           ) (List.tl psl);
         Format.fprintf ppf ")"
       end
  in
  let print_assign_instr lhs expr =
    Format.fprintf ppf "@[%a <- %a;@]" print_lhs lhs pp_ex expr
  in
  let print_sample_instr lhs expr =
    Format.fprintf ppf "@[%a <$ %a;@]" print_lhs lhs pp_ex expr
  in
  let print_match_instr expr (mcl:match_clause_tyd list) =
    let ety = EcTypes.e_ty expr in
    let p, _, typ = EcUtils.oget (EcEnv.Ty.get_top_decl ety (EcScope.env sc)) in
    let pp_branch ppf (ctor, (bndngs, codeblock)) =
      let bndngs = List.map (fun (idloc, ty) ->
                       (EcLocation.unloc idloc, ty)) bndngs in
      let pttn = EcTypes.toarrow (snd (List.split bndngs)) ety in
      let pttn = EcFol.f_op (EcPath.pqoname (EcPath.prefix p) ctor) typ pttn in
      let pttn = EcFol.f_app pttn (List.map
                (fun (x, ty) -> EcFol.f_local x ty) bndngs) ety
      in

      Format.fprintf ppf "@[| %a => {@]@;@[<v 2>@;" (pp_form sc) pttn;
      print_code sim_uses
        sc root mbmap ppf codeblock state_name dii ais ptn intprts glob_pfx; 
      Format.fprintf ppf "@]@;@[}@]@;"
    in

    Format.fprintf ppf "@[match (@[%a@]) with@]@;@[<v>%a@]@[end;@]@]"
      (pp_expr sc) expr (EcPrinting.pp_list "" pp_branch) mcl
(*
    let print_mc ppf mc =
      let print_bindings ppf bndngs =
        List.iter (fun (id,_) ->
            Format.fprintf ppf "%a " EcIdent.pp_ident (EcLocation.unloc id)
          ) bndngs
      in 
      let (ctor, (bndngs, codeblock)) = mc in
      Format.fprintf ppf "@[| %s %a=> {@]@;<0 2>@[<v>"
        ctor print_bindings bndngs;
      print_code sc root mbmap ppf codeblock state_name dii ptn intprts; 
      Format.fprintf ppf  "@]@;}@;"
    in
    Format.fprintf ppf "@[match (%a :~ %a) with@]@;@[<v>"
      pp_ex expr (pp_type sc) (EcTypes.e_ty expr);
    List.iter (fun mc -> Format.fprintf ppf "%a" print_mc mc) mcl;
    Format.fprintf ppf "@]@;@[end;@]"
 *)
  in
  let print_instruction ppf (it : instruction_tyd) : unit =
    match EcLocation.unloc it with
    | Assign (lhs, expr) -> print_assign_instr lhs expr
    | Sample (lhs, expr) -> print_sample_instr lhs expr
    | ITE (expr, thencode, elsecodeo) -> print_ite_instr expr thencode elsecodeo
    | Match (expr, mcl) -> print_match_instr expr (EcLocation.unloc mcl)
    | SendAndTransition sat -> print_sat_instr sat
    | Fail -> print_fail_instr ()
  in
  let code = EcLocation.unloc code in
  List.iter (fun it -> Format.fprintf ppf "%a@;" print_instruction it) code
  

let print_mmc_proc (sim_uses : string option)
      (sc : EcScope.scope) (root : string)
      (mbmap : message_body_tyd SLMap.t) (ppf : Format.formatter)
      (state_id : string) (params : ty_index Mid.t)
      (vars : (EcIdent.t * ty) EcLocation.located IdMap.t)
      (mmc : msg_match_clause_tyd) (state_name : string -> string)
      (dii : symb_pair IdMap.t) (ais : symb_pair IdPairMap.t)
      (ptn : string option) (intprts : EcIdent.t QidMap.t)
      (glob_pfx : string) : unit =
  Format.fprintf ppf "@[proc %s (%a) : %a option = {@]@;<0 2>@[<v>"
    (mmc_proc_name state_id mmc.msg_pat.msg_path_pat state_name)
    (print_proc_params_decl sc) ((sparams_map_to_list params)@(
      List.map (fun (id,t) -> ((EcIdent.name id),t)) (msg_match_clause_msg_pat_bindings mmc)))
    (pp_type sc) msg_ty;
  IdMap.iter (fun id l -> let (ident,ty) = EcLocation.unloc l in
      Format.fprintf ppf "@[var %s : %a;@]@;"
              (EcIdent.name ident) (pp_type sc) ty
    ) vars;
  Format.fprintf ppf "@[var %s : %a option <- None;@]@;" _r (pp_type sc) msg_ty;
  print_code sim_uses
    sc root mbmap ppf mmc.code state_name dii ais ptn intprts glob_pfx;
  Format.fprintf ppf "@[return %s;@]" _r;
  Format.fprintf ppf "@]@;}@;"

let print_mmc_procs ?(sim_uses : string option = None)
      (sc : EcScope.scope) (root : string)
      (mbmap : message_body_tyd SLMap.t) (ppf : Format.formatter)
      (states : state_tyd IdMap.t) (state_name : string -> string)
      (dii : symb_pair IdMap.t) (ais : symb_pair IdPairMap.t)
      (ptn : string option) (glob_pfx : string) : unit =
  IdMap.iter(fun id st -> let st:state_body_tyd = EcLocation.unloc st in
    List.iter(fun mmc ->
      if UcSpecTypedSpecCommon.msg_path_pat_ends_star mmc.msg_pat.msg_path_pat
      then ()
      else print_mmc_proc sim_uses sc root mbmap ppf id
             st.params st.vars mmc state_name dii ais ptn
             st.internal_ports glob_pfx
      ;) st.mmclauses
    ) states

let print_mmc_proc_call  ?(objstr : string = _x) (ppf : Format.formatter)
      (state_id : string) (params : ty_index Mid.t) (mmc : msg_match_clause_tyd)
      (pfx : string) (msgn : string) (mb : message_body_tyd)
      (state_name : string -> string) (glob_pfx : string) : unit =
  let mmc_msg_pat_bindings (mmc : msg_match_clause_tyd)
      : string list =
    let msg_pat = mmc.msg_pat in
    let records =
    (match msg_pat.port_id with
     | None   -> []
     | Some x -> [(name_record_dir_port msgn mb)]) @
    (match msg_pat.pat_args with
     | None    -> []
     | Some xs ->
       let pm = fst (List.split (params_map_to_list mb.params_map)) in 
       let ys =
         List.mapi
           (fun i pat ->
            match pat_id_data pat with
            | None   -> []
            | Some z -> [name_record msgn (List.nth pm i)])
         xs in
       List.concat ys) in
    let pfx = objstr^".`"^pfx in
    List.map (fun r -> pfx^r) records
  in
  let params_list = fst (List.split (sparams_map_to_list params)) in
  let params_list = params_list @ (mmc_msg_pat_bindings mmc) in
  Format.fprintf ppf "@[%s %s %s (%a);@]"
    _r "<@" (mmc_proc_name state_id mmc.msg_pat.msg_path_pat state_name)
    print_proc_params_call params_list


let print_state_match_branch (root : string) (id : string)
      (mbmap : message_body_tyd SLMap.t) (state_name : string -> string)
(dii : symb_pair IdMap.t) (glob_pfx : string) (ppf : Format.formatter) (st : state_tyd) : unit =
  let st = EcLocation.unloc st in
  let spnt = sparams_map_to_list st.params in
  let print_state_params_names ppf spnt =
    List.iter (fun (n,_) -> Format.fprintf ppf "%s@ " n) spnt
  in
  let rec print_mm ppf (mmcs : msg_match_clause_tyd list) : unit =
    if List.is_empty mmcs
    then ()
    else
      let mmc = List.hd mmcs in
      let mp = get_msg_path mmc.msg_pat.msg_path_pat in
      let msg_name, is_internal, iiphd, pfx, mb, epdp_str =
        get_msg_info mp dii IdPairMap.empty root mbmap in
      Format.fprintf ppf "@[match %s.`dec %s with@]@;"
        epdp_str _m;
      Format.fprintf ppf "@[| Some %s => {@]@;<0 2>@[<v>" _x;
      if is_internal then
        Format.fprintf ppf "@[if (%s.`3.`1 = %s){@]@;<0 2>@[<v>"
          _m (addr_op_call ~pfx:glob_pfx iiphd);
      print_mmc_proc_call ppf id st.params mmc pfx msg_name mb state_name glob_pfx;
      if is_internal then
        Format.fprintf ppf "@]@;}@;";
      Format.fprintf ppf "@]@;}@;";
      Format.fprintf ppf "@[| None => {@]@;<0 2>@[<v>";
      print_mm ppf (List.tl mmcs);
      Format.fprintf ppf "@]@;}@;end;"
  in
  let mmcs = List.filter (fun mmc -> not
    (UcSpecTypedSpecCommon.msg_path_pat_ends_star mmc.msg_pat.msg_path_pat)
  ) st.mmclauses in
  Format.fprintf ppf "@[| %s %a=> {@]@;<0 2>@[<v>"
    (state_name id) print_state_params_names spnt;
  print_mm ppf mmcs;
  Format.fprintf ppf "@]@;}@;"



let print_proc_parties (sc : EcScope.scope)(root : string) (id : string)
      (mbmap : message_body_tyd SLMap.t) (procn : string)
      (state_name : string -> string) (dii : symb_pair IdMap.t)
      ?(pfx = "") (ppf : Format.formatter) (states : state_tyd IdMap.t)
      (pno : string option) : unit =
  Format.fprintf ppf "@[proc %s(%s : %a) : %a option = {@]@;<0 2>@[<v>"
    procn _m (pp_type sc) msg_ty (pp_type sc) msg_ty;
    Format.fprintf ppf "@[var %s : %a option <- None;@]@;"
      _r (pp_type sc) msg_ty;
    let state_var_name =
      match pno with
      | None -> _st
      | Some pn -> st_name pn in
    Format.fprintf ppf "@[match %s%s with@]@;" pfx state_var_name;
    IdMap.iter (fun id st -> Format.fprintf ppf "%a"
      (print_state_match_branch root id mbmap state_name dii pfx)
      st) states;
    Format.fprintf ppf "@[end;@]@;";
    Format.fprintf ppf "@[return %s;@]" _r;
    Format.fprintf ppf "@]@;}@;"


  

let print_ideal_module (sc : EcScope.scope) (root : string) (id : string)
      (mbmap : message_body_tyd SLMap.t) (dii : symb_pair IdMap.t)
      (ppf : Format.formatter) (ifbt : ideal_fun_body_tyd) : unit =
  let print_vars () =
     Format.fprintf ppf "@[var %s : %a@]@;" _self (pp_type sc) addr_ty;
     Format.fprintf ppf "@[var %s : %s@]@;" _st state_type_name_IF;
  in
  let print_proc_init () =
    Format.fprintf ppf "@[proc init(self_ : %a) : unit = {@]@;<0 2>"
    (pp_type sc) addr_ty;
    Format.fprintf ppf "@[%s <- self_; %s <- %s;@]@;@[}@]@;"
    _self _st (state_name (initial_state_id_of_states ifbt.states));
  in
  let print_proc_invoke () =
    let r, m = "r", "m" in
    let print_dir_pi_guard ppf () : unit =
      let basics = SLMap.filter_map (fun iip _ ->
        if List.hd iip = root && List.hd (List.tl iip) = ifbt.id_dir_inter
        then Some (List.hd (List.tl (List.tl iip)))
        else None
                       ) mbmap in
      let basics = snd (List.split (SLMap.bindings basics)) in
      let basics = List.sort_uniq String.compare basics in
      let bhd = List.hd basics in
      let btl = List.tl basics in
      let compn = uc_name ifbt.id_dir_inter in
      Format.fprintf ppf "%s.`2.`2 = %s.%s.pi" m compn bhd;
      List.iter (fun bn ->
        Format.fprintf ppf "@ \\/@ %s.`2.`2 = %s.%s.pi" m compn bn) btl
    in
    Format.fprintf ppf "@[proc %s(%s : %a) : %a option = {@]@;<0 2>@[<v>"
      invoke m (pp_type sc) msg_ty (pp_type sc) msg_ty;
    Format.fprintf ppf "@[var %s : %a option <- None;@]@;"
      r (pp_type sc) msg_ty;
    Format.fprintf ppf
      "@[if ((%s.`1 = %s@ /\\@ %s.`2.`1 = %s@ /\\@ (%a)@ /\\@ envport %s %s.`3)@]"
      m mode_Dir m _self print_dir_pi_guard()  _self m;
    if ifbt.id_adv_inter<>None
    then begin 
     Format.fprintf ppf "\\/";
     Format.fprintf ppf
       "@[@ (%s.`1 = %s@ /\\@ %s.`2.`1 = %s@ /\\@ %s.`2.`2 = %s.pi@ /\\@ %s.`3.`1 = %s))@]{"
       m mode_Adv m _self m (uc_name (EcUtils.oget ifbt.id_adv_inter)) m adv
      end
    else
      Format.fprintf ppf "@[)@]{"
    ;
    Format.fprintf ppf "@;<0 2>@[%s %s %s(%s);@]" r "<@" parties_str m;
    Format.fprintf ppf "@;}@]@;@[return %s;@]@;}@;" r
  in

  Format.fprintf ppf "@[module %s : FUNC= {@]@;<0 2>@[<v>" (uc_name id);
  print_vars ();
  print_proc_init ();
  print_mmc_procs
    sc root mbmap ppf ifbt.states state_name dii IdPairMap.empty None "";
  print_proc_parties sc root id mbmap parties_str state_name dii ppf ifbt.states None;
  print_proc_invoke ();
  Format.fprintf ppf "@]@\n}.";
  ()

let clone_adv_inter (ppf : Format.formatter) (id : string) =
  Format.fprintf ppf "@[clone %s as %s with@]@;"
      (bi_name id) (uc_name id);
    Format.fprintf ppf "@[  op %s = %s@]@;"
      _pi adv_if_pi_op_name;
    Format.fprintf ppf "@[proof *.@]@;@;"

let print_proof_state_match (root : string)
      (mbmap : message_body_tyd SLMap.t) (dii : symb_pair IdMap.t)
      (ret_pfx : string) (ppf : Format.formatter)
      (st_map : state_tyd IdMap.t) : unit =
    let print_proof_state_match_branch (ppf : Format.formatter)
        (state : state_tyd) : unit =
      let st = EcLocation.unloc state in
      let rec print_proof_mm ppf (mmcs : msg_match_clause_tyd list) : unit =
        let print_proof_mmc ppf (mmc : msg_match_clause_tyd) : unit =
          let rec print_proof_code ppf
                    (code : instruction_tyd list EcLocation.located) : unit =
            let print_instruction ppf (it : instruction_tyd) : unit =
              match EcLocation.unloc it with
              | Assign (lhs, expr) ->
                 Format.fprintf ppf "@[sp 1. (*Assign instruction*)@]@;"
              | Sample (lhs, expr) ->
                 Format.fprintf ppf
                 "@[seq 1 : (#pre). rnd. skip. smt(). (*Sample instruction*)@]@;"
              | ITE (expr, thencode, elsecodeo) -> begin
                  Format.fprintf ppf "@[if. (*if instruction*)@]@;";
                   print_proof_code ppf thencode;
                   if elsecodeo <> None then
                     print_proof_code ppf (EcUtils.oget elsecodeo)
                   end
              | Match (expr, mcl) -> begin
                  let mcl = EcLocation.unloc mcl in
                  let mcl = List.rev mcl in (*TODO: check how ec chooses order*)
                  Format.fprintf ppf
                    "@[match. (*match instruction with %i branches*)@]@;"
                    (List.length mcl);
                  List.iter (fun (s,(_,code))->
                      Format.fprintf ppf "@[(*branch %s*)@ %a@]@;"
                        s print_proof_code code) mcl
                end
              | SendAndTransition sat -> begin
                 let mp = sat.msg_expr.path in
                 let _, is_internal, _, _, mb, _ =
                   get_msg_info mp dii IdPairMap.empty root mbmap in
                 let envportcheck = (not is_internal) && (mb.port <> None) in
                 if envportcheck
                 then Format.fprintf ppf "@[if. (*envport check*)@]@;"
                 ;  
                 Format.fprintf ppf
                   "@[%s sp 3. skip. smt(%s). (*SendAndTransition instruction*)@]@;"
                   ret_pfx smt_sat_lemmas;
                 if envportcheck
                 then
                   Format.fprintf ppf
                   "@[%s sp 1. skip. smt(). (*envport check failed case*)@]@;"
                   ret_pfx
                end
              | Fail ->
                 Format.fprintf ppf
                   "@[%s sp 2. skip. smt(). (*Fail instruction*)@]@;" ret_pfx
            in
            
            let code = EcLocation.unloc code in
            List.iter (fun it -> Format.fprintf ppf "%a@;"
                                   print_instruction it) code
          in

          let pat_no = List.length (msg_match_clause_msg_pat_bindings mmc) in
          if pat_no > 0
          then Format.fprintf ppf "@[sp %i. (*pattern bindings*)@]@;" pat_no
          ;
          let is_empty = (EcLocation.unloc mmc.code = [])in
          if is_empty
          then Format.fprintf ppf
                 "@[skip. smt(). (*empty message match clause*)@]@;"
          else print_proof_code ppf mmc.code
        in
        
        if List.is_empty mmcs
        then ()
        else
          let mmc = List.hd mmcs in
          let mp = get_msg_path mmc.msg_pat.msg_path_pat in
          let msg_name, is_internal, iiphd, pfx, mb, epdp_str =
            get_msg_info mp dii IdPairMap.empty root mbmap in
          Format.fprintf ppf "@[match. (*message match*)@]@;";
          Format.fprintf ppf
            "@[%s skip. smt(). (*None branch of message match, dec failed*)@]@;"
            ret_pfx;
          if is_internal then
            Format.fprintf ppf
              "@[if. (*address check for internal messages*)@]@;"
          ;
            Format.fprintf ppf
            "@[sp %i. (*state param assignment, return value initialization*)@]"
              ((Mid.cardinal st.params) + 1);
          print_proof_mmc ppf mmc;
          print_proof_mm ppf (List.tl mmcs);
          if is_internal then
            Format.fprintf ppf
              "@[%s skip. smt(). (*address check for internal messages failed case*)@]@;"
              ret_pfx
          ;
      in
      
  let mmcs = List.filter (fun mmc -> not
    (UcSpecTypedSpecCommon.msg_path_pat_ends_star mmc.msg_pat.msg_path_pat)
               ) st.mmclauses in
  if List.is_empty mmcs
  then 
    Format.fprintf ppf
            "@[%s skip. smt(). (*empty state match branch code*)@]@;" ret_pfx
  else
    print_proof_mm ppf mmcs;
  in
  Format.fprintf ppf "@[%s sp 1. (*initializing input, return value*)@]@;"
    ret_pfx;
  Format.fprintf ppf "@[match. (*state match*)@]@;";
  IdMap.iter (fun id st -> Format.fprintf ppf "(*state branch %s*) %a" id
                            print_proof_state_match_branch st) st_map

let print_IF_lemma_metric_invoke (metric_name : string) (module_name : string) 
      (root : string)
      (mbmap : message_body_tyd SLMap.t) (dii : symb_pair IdMap.t)
      (ppf : Format.formatter) (st_map : state_tyd IdMap.t) : unit =    
  Format.fprintf ppf "@[lemma %s (n : int) : hoare [@]@;<0 2>@[<v>" _invoke;
  Format.fprintf ppf
    "%s.%s :@ %s (glob %s) /\\ %s (glob %s) = n@ ==>@ "
    module_name invoke _invar module_name metric_name module_name;
  Format.fprintf ppf
    "(res <> None =>@ %s (glob %s) < n@;"
    metric_name module_name;
  Format.fprintf ppf
    "/\\ ((oget res).`1 = %s => (oget res).`2.`2 \\in oflist [%s]))@;"
    _Adv adv_if_pi_op_name;
  Format.fprintf ppf "@]@;].@;";
  Format.fprintf ppf "@[proof.@]@;";
  Format.fprintf ppf "@[rewrite /%s /=.@]@;" metric_name;
  Format.fprintf ppf "@[proc.@]@;";
  Format.fprintf ppf "@[sp 1. (*initializing return value*)@]@;";
  Format.fprintf ppf "@[if. (*invoke guard*)@]@;";
  Format.fprintf ppf "@[inline.@]@;";
  print_proof_state_match root mbmap dii "sp 1." ppf st_map;
  Format.fprintf ppf "@[skip. smt(). (*invoke guard false*)@]@;";
  Format.fprintf ppf "@[qed.@]@;"

let print_ctor_args_state_metric (st_id : string)  (ppf : Format.formatter)
      (st_map : state_tyd IdMap.t) : unit =
    let s = IdMap.find st_id st_map in
    let sb = EcLocation.unloc s in
    Mid.iter (fun _ _ -> Format.fprintf ppf "_ " ) sb.params



let print_IF_state_metric (module_name : string)
  (ppf : Format.formatter) (st_map : state_tyd IdMap.t) : unit =
  let lin = linearize_state_DAG st_map in
  match lin with
  | None -> Format.fprintf ppf
              "@[(*cannot generate operator %s, states have cycles*)@]"
              uc_metric_name 
  | Some id_lvl_map ->
     begin
     let globopname = glob_to_part_op_name module_name _st in
     Format.fprintf ppf "@[op %s (g : glob %s) / : %s = g.`2.@]@;"
     globopname module_name state_type_name_IF;
     Format.fprintf ppf
       "@[<v>@[op [smt_opaque] %s (g : glob %s) : int =@]@;<0 2>@[<v>"
       uc_metric_name  module_name;
     Format.fprintf ppf "@[match %s g with@]@;" globopname;
     IdMap.iter (fun id lvl ->
         Format.fprintf ppf "@[| %s %a=> %i@]@;"
           (state_name id) (print_ctor_args_state_metric id) st_map lvl
       ) id_lvl_map;
     Format.fprintf ppf "@[end.@]@;@]@;@]"
     end


let print_IF_metric (id : string)(root : string)
      (mbmap : message_body_tyd SLMap.t) (dii : symb_pair IdMap.t)
      (ppf : Format.formatter) (st_map : state_tyd IdMap.t)
    : unit =
    Format.fprintf ppf "@[%a@]@;@;"
    (print_IF_state_metric (uc_name id))
    st_map;
  Format.fprintf ppf "@[%a@]@;@;"
    (print_IF_lemma_metric_invoke uc_metric_name (uc_name id) root mbmap dii)
    st_map

let print_IF_invar
      (ppf : Format.formatter) (id : string) : unit =
  Format.fprintf ppf "@[<v>@;";
  Format.fprintf ppf "@[(*alias*)@]@;";
  Format.fprintf ppf "@[module IF = %s.@]@;" (uc_name id);
  Format.fprintf ppf "@[op %s (g : glob IF) : bool = predT g.@]@;@;" _invar;
  Format.fprintf ppf "@]@;"


let print_IF_metric_good_init_lemmas
      (ppf : Format.formatter) (_ : unit): unit =
  Format.fprintf ppf "@[lemma %s (g : glob IF) :@]@;"  _metric_good;
  Format.fprintf ppf "@[  %s g => 0 <= %s g.@]@;" _invar uc_metric_name;
  Format.fprintf ppf "@[  proof. rewrite /%s.%s /=.@]@;" uc__if uc_metric_name;
  Format.fprintf ppf "@[  smt(). qed.@]@;";
  Format.fprintf ppf "@[lemma _init :@]@;";
  Format.fprintf ppf "@[  hoare [IF.init : true ==> %s (glob IF)].@]@;" _invar;
  Format.fprintf ppf "@[proof. proc. auto. qed.@]@;";
  Format.fprintf ppf "@]@;"

let gen_ideal_fun (sc : EcScope.scope) (root : string) (id : string)
      (mbmap : message_body_tyd SLMap.t) (ifbt : ideal_fun_body_tyd)
      (dii : symb_pair IdMap.t) : string =
  let sf = Format.get_str_formatter () in
  Format.fprintf sf "@[<v>";
  if ifbt.id_adv_inter<>None
  then clone_adv_inter sf (EcUtils.oget ifbt.id_adv_inter);
  Format.fprintf sf "@[%s@]@;@;" (open_theory uc__if);
  Format.fprintf sf "@[%a@]@;@;" (print_state_type_IF sc) ifbt.states;
  Format.fprintf sf "@[%a@]@;@;" (print_ideal_module sc root id mbmap dii) ifbt;
  Format.fprintf sf "@[%a@]@;@;" print_IF_invar id;
  Format.fprintf sf "%a" (print_IF_metric id root mbmap dii) ifbt.states;
  Format.fprintf sf "@[%a@]@;@;" print_IF_metric_good_init_lemmas ();
  Format.fprintf sf "@[%s@]@;" (close_theory uc__if);
  Format.fprintf sf "@]";
  Format.flush_str_formatter ()

let print_addr_and_port_operators (sc : EcScope.scope) (ppf : Format.formatter)
      (rapm : rf_addr_port_maps) : unit =
  let print_addr_op (name : string) (n : int) : unit =
    Format.fprintf ppf "@[op %s (%s : %a) : %a = %s ++ [%i].@]@;"
      (addr_op_name name) self (pp_type sc) addr_ty (pp_type sc) addr_ty self n
  in
  let print_port_op (port_op_name : string -> string) (name : string) (n : int)
      : unit =
    Format.fprintf ppf "@[op %s (%s : %a) : %a = (%s, %i).@]@;"
      (port_op_name name) self (pp_type sc) addr_ty (pp_type sc) port_ty self n
  in
  let print_extport_op (name : string) (n : int) : unit =
    print_port_op extport_op_name name n
  in
  let print_intport_op (name : string) (n : int) : unit =
    print_port_op intport_op_name name n
  in
  Format.fprintf ppf "@[<v>";
  IdMap.iter (fun pn n ->
    print_addr_op pn n) rapm.params_addr_sufix;
  Format.fprintf ppf "@;";
  IdMap.iter (fun pn n ->
    print_addr_op pn n) rapm.subfun_addr_sufix;
  Format.fprintf ppf "@;";
  IdMap.iter (fun pn n ->
    if n<>None
    then print_extport_op pn (EcUtils.oget n)) rapm.party_ext_port_id;
  Format.fprintf ppf "@;";
  IdMap.iter (fun pn n ->
    print_intport_op pn n) rapm.party_int_port_id;
  Format.fprintf ppf "@]@;"

let print_party_types (sc : EcScope.scope) (ppf : Format.formatter)
      (parties : party_tyd IdMap.t) : unit =
  Format.fprintf ppf "@[<v>";
  IdMap.iter (fun (pn : string) (pt : party_tyd) ->
      print_state_type sc ppf (EcLocation.unloc pt).states
        (state_type_name_pt pn) (state_name_pt pn);
    ) parties;
  Format.fprintf ppf "@]"

let _print_params str ppf params : unit =
    if (IdMap.cardinal params)=0
    then ()
    else
      let params = IdMap.bindings params in
      let params = List.sort (fun (_,(_,n1)) (_,(_,n2)) -> n1-n2) params in
      let pns = fst (List.split params) in
      Format.fprintf ppf "(";
      Format.fprintf ppf "%s%s" (List.hd pns) str;
      List.iter (fun pn ->
        Format.fprintf ppf ", %s%s" pn str) (List.tl pns);
      Format.fprintf ppf ")"

let print_params_FUNC ppf params : unit = _print_params " : FUNC" ppf params

let print_params_list ppf params : unit =  _print_params "" ppf params

(*real and rest module print begin -----------------------------*)

  let print_vars ppf (sc : EcScope.scope) (parties : party_tyd IdMap.t) =
     Format.fprintf ppf "@[var %s : %a@]@;" _self (pp_type sc) addr_ty;
     IdMap.iter (fun pn _ ->
         Format.fprintf ppf "@[var %s : %s@]@;"
           (st_name pn) (state_type_name_pt pn)  
       ) parties;
     Format.fprintf ppf "@;"

  let subfunpath sfn sfid = (uc_name sfn)^"."^uc__code^"."^uc__if^"."^(uc_name sfid)
  
  let print_proc_init ppf (sc : EcScope.scope) ?(module_pfx = "")
    (params : (symb_pair * int) IdMap.t)
    (sub_funs : symb_pair IdMap.t)
    (parties : party_tyd IdMap.t) =
    Format.fprintf ppf "@[proc init(self_ : %a) : unit = {@]@;<0 2>"
    (pp_type sc) addr_ty;
    Format.fprintf ppf "@[%s%s <- self_;@]@;" module_pfx _self;
    IdMap.iter (fun sfn (sfr, sfid) ->
      Format.fprintf ppf "@[%s.init(%s);@]@;"
        (subfunpath sfn sfid)
        (addr_op_call ~pfx:module_pfx sfn)) sub_funs;
    IdMap.iter (fun pn _ ->
      Format.fprintf ppf "@[%s.init(%s);@]@;"
       pn (addr_op_call ~pfx:module_pfx pn)) params;
    IdMap.iter (fun pn pt ->
    Format.fprintf ppf "@[%s%s <- %s;@]@;"
      module_pfx (st_name pn) (state_name_pt pn (initial_state_id_of_party_tyd  pt))
      ) parties;
    Format.fprintf ppf "@[}@]@;"
 
  let print_proc_invoke ppf (sc : EcScope.scope) ?(module_pfx = "")
    (pepi : int option  IdMap.t)
    (params : (symb_pair * int) IdMap.t)
    (sub_funs : symb_pair IdMap.t)
    (parties : party_tyd IdMap.t) =
    let r, m = "r", "m" in
    let print_subfun_or_param_invoke ppf (nm : string) (path : string): unit =
      Format.fprintf ppf
        "@[if@ (%s <= %s.`2.`1)@ {%s %s %s.%s(%s);}@]@;"
        (addr_op_call ~pfx:module_pfx nm) m r "<@" path invoke m;
      Format.fprintf ppf
        "@[else {@]@;"
    in
    let print_party_invoke ppf (nm : string) : unit =
      let has_extport = (IdMap.find nm pepi) <> None in
      if has_extport
      then begin
      Format.fprintf ppf
      "@[if ((%s.`1 = %s@ /\\@ %s.`2 = %s@ /\\@ envport %s%s %s.`3)@]@;"
      m mode_Dir m (extport_op_call ~pfx:module_pfx nm)
      module_pfx _self m;
      Format.fprintf ppf "@[\\/@]@;";
      Format.fprintf ppf
        "@[(%s.`1 = %s@ /\\@ %s.`2 = %s@ /\\@ %s.`3.`1 = %s)@]@;"
        m mode_Adv m (extport_op_call ~pfx:module_pfx nm) m adv;
      Format.fprintf ppf "@[\\/@]@;"
        end
      else
        Format.fprintf ppf "@[if(@]"
      ;
      Format.fprintf ppf
      "@[(%s.`1 = %s@ /\\@ %s.`2 = %s@ /\\@ %s%s <= %s.`3.`1))@]@;"
      m mode_Dir m (intport_op_call ~pfx:module_pfx nm)
      module_pfx _self m;
      Format.fprintf ppf "@[{%s %s %s(%s);}@]@;"
        r "<@" (proc_party_str nm) m
    in

    Format.fprintf ppf "@[proc %s(%s : %a) : %a option = {@]@;<0 2>@[<v>"
      invoke m (pp_type sc) msg_ty (pp_type sc) msg_ty;
    Format.fprintf ppf "@[var %s : %a option <- None;@]@;"
      r (pp_type sc) msg_ty;
    IdMap.iter (fun sfn (_,sfid) ->
        print_subfun_or_param_invoke ppf sfn (subfunpath sfn sfid)
      ) sub_funs;
    IdMap.iter (fun pn _ ->
        print_subfun_or_param_invoke ppf pn pn) params;
    let partyl = IdMap.to_list parties in
    let pc = IdMap.cardinal parties in
    List.iteri (fun i (pn, _) ->
        print_party_invoke ppf pn;
        if i+1<pc then Format.fprintf ppf "@[else {@]@;") partyl;
    let else_num = (IdMap.cardinal sub_funs) +
                   (IdMap.cardinal params) +
                     pc - 1 in
    for _ = 1 to else_num do
      Format.fprintf ppf "@[}@]@;"
    done;
    Format.fprintf ppf "@[return %s;@]@;}@;" r
 

let print_real_module (sc : EcScope.scope) (root : string) (id : string)
      (mbmap : message_body_tyd SLMap.t) (dii : symb_pair IdMap.t)
      (pepi : int option  IdMap.t)
      (ppf : Format.formatter) (rfbt : real_fun_body_tyd) : unit =

  Format.fprintf ppf "@[module %s %a : FUNC = {@]@;<0 2>@[<v>"
    (uc_name id) print_params_FUNC rfbt.params;
  print_vars ppf sc rfbt.parties;
  print_proc_init ppf sc rfbt.params rfbt.sub_funs rfbt.parties;
  IdMap.iter (fun (pn : string) (pt : party_tyd) ->
      let states = (EcLocation.unloc pt).states in
      let sn = (state_name_pt pn) in
      let ps = proc_party_str pn in
      print_mmc_procs sc root mbmap ppf states sn dii IdPairMap.empty (Some pn) "";
      print_proc_parties sc root id mbmap ps sn dii ppf states (Some pn)
  ) rfbt.parties;
  print_proc_invoke ppf sc pepi rfbt.params rfbt.sub_funs rfbt.parties;
  Format.fprintf ppf "@]@\n}.";
  ()

let print_rest_module (sc : EcScope.scope) (root : string) (id : string)
      (mbmap : message_body_tyd SLMap.t) (dii : symb_pair IdMap.t)
      (pepi : int option  IdMap.t)
      (rfbt : real_fun_body_tyd) (ppf : Format.formatter) 
      (drop_param : int) : unit =
  let rest_params = IdMap.filter (fun _ (_,idx) ->
                        (idx+1) <> drop_param)
                      rfbt.params in
  let rest_module_name = (uc_name id)^"_Rest"^(string_of_int drop_param) in
  Format.fprintf ppf "@[module %s %a : FUNC = {@]@;<0 2>@[<v>"
    rest_module_name print_params_FUNC rest_params;
  let module_pfx = (uc_name id)^"." in
  print_proc_init ppf sc ~module_pfx:module_pfx
    rest_params rfbt.sub_funs rfbt.parties;
  IdMap.iter (fun (pn : string) (pt : party_tyd) ->
      let states = (EcLocation.unloc pt).states in
      let sn = (state_name_pt pn) in
      let ps = proc_party_str pn in
      print_mmc_procs sc root mbmap ppf states sn dii
        IdPairMap.empty (Some pn) module_pfx;
      print_proc_parties sc root id mbmap ps sn dii
        ppf states (Some pn) ~pfx:module_pfx
  ) rfbt.parties;
  print_proc_invoke ppf sc ~module_pfx:module_pfx
    pepi rest_params rfbt.sub_funs rfbt.parties;
  Format.fprintf ppf "@]@\n}.";
  ()

(*real and rest module print end -------------------------------*)

let print_glob_operator op_name top_type sub_type ppf range =
      Format.fprintf ppf "@[<v>";
      Format.fprintf ppf "@[op %s(g : glob %s) / : glob %s =@]@;"
        op_name top_type sub_type;
      let rhd = List.hd range in
      let rtl = List.tl range in
      Format.fprintf ppf "(g.`%i%s)."
      rhd (List.fold_left (fun acc i -> acc^", g.`"^(string_of_int i)) "" rtl);
      Format.fprintf ppf "@]"

let print_rf_info_operator ppf (rfbt : real_fun_body_tyd) : unit =
  let deduce_param_pis ppf rfbt =
      IdMap.iter (fun pmn _ -> Format.fprintf ppf " - %s.%s.%s"
        (uc_name pmn) uc__code adv_pi_num_op_name) rfbt.params
  in
  let begin_param_pis ppf rfbt =
      if IdMap.is_empty rfbt.params
      then ()
      else
        List.iteri (fun i (pmn, _) ->
            if i>0 then Format.fprintf ppf "; "
            ;
            Format.fprintf ppf "%s"
            (adv_pi_begin_param pmn)) (IdMap.bindings rfbt.params)
  in
  let end_param_pis ppf rfbt =
      if IdMap.is_empty rfbt.params
      then ()
      else
        List.iteri (fun i (pmn, _) ->
            let nm = uc_name pmn in
            if i>0 then Format.fprintf ppf "; "
            ;
            Format.fprintf ppf "%s + %s.%s.%s - 1"
            (adv_pi_begin_param pmn) nm uc__code adv_pi_num_op_name)
          (IdMap.bindings rfbt.params)
  in
  Format.fprintf ppf "@[op %s = {|@]@;" rf_info;
  Format.fprintf ppf "@[rfi_num_parties = %i;@]@;"
    (IdMap.cardinal rfbt.parties);
  Format.fprintf ppf "@[rfi_num_subfuns = %i;@]@;"
    (IdMap.cardinal rfbt.sub_funs);
  Format.fprintf ppf "@[rfi_num_params = %i;@]@;"
    (IdMap.cardinal rfbt.params);
  Format.fprintf ppf "@[rfi_adv_pi_begin = %s;@]@;" adv_pi_begin_op_name;
  Format.fprintf ppf "@[rfi_adv_pi_main_end = %s + %s - 1%a;@]@;"
    adv_pi_begin_op_name adv_pi_num_op_name deduce_param_pis rfbt;
  Format.fprintf ppf "@[rfi_adv_pi_begin_params = [%a];@]@;"
    begin_param_pis rfbt;
  Format.fprintf ppf "@[rfi_adv_pi_end_params = [%a];@]@;"
    end_param_pis rfbt;
  Format.fprintf ppf "@[|}.@]@;"

let print_cloneRF_MakeRF ppf
(id,rfbt,gvil : string * real_fun_body_tyd * globVarId list) : unit =
(*
  op rf_info <-
  {|
    rfi_num_parties = 2;
    rfi_num_subfuns = 2;
    rfi_num_params  = 0;
    rfi_adv_pi_begin = _adv_pi_begin;  (* first adv pi of instance of unit *)
    rfi_adv_pi_main_end = _adv_pi_begin + _adv_pi_num;  (* last advi pi not from params *)
    rfi_adv_pi_begin_params = [];
    rfi_adv_pi_end_params = [];
    |}
*)
  let print_cloneRF =
    Format.fprintf ppf "@;@[clone RealFunctionality as RFCore with@]@;";
    Format.fprintf ppf "@[op %s <- %s.%s@]@;" rf_info uc__rf rf_info;
  Format.fprintf ppf "@[proof *.@]@;";
  Format.fprintf ppf "@[realize rf_info_valid. smt(%s). qed.@]@;@;"
    adv_pi_begin_gt0_axiom_name
  in
  let print_MakeRF_and_lemmas =
    let real = uc__rf^"."^(moduleRP id rfbt) in
    Format.fprintf ppf
      "@[module %s = RFCore.MakeRF(%s).@]@;@;"
      _RFRP
    real;
    Format.fprintf ppf
"@[lemma RFRP_Core_init_invar_hoare :
  hoare [RFRP.init : true ==> %s.%s (glob %s)].
proof.
apply (RFCore.MakeRF_init_invar_hoare (%s) %s.%s).
apply %s.%s.
qed.@]@;@;"
      uc__rf (invarIRP rfbt true)  real
      real uc__rf (invarIRP rfbt true)
      uc__rf (initIRP rfbt true);
    Format.fprintf ppf
"@[lemma RFRP_Core_invoke_term_metric_hoare (n : int) :
  hoare
  [RFRP.invoke :
   %s.%s (glob %s) /\\ %s.%s (glob %s) = n ==>
   %s.%s (glob %s) /\\@;
 (res <> None => %s.%s (glob %s) < n@;
 /\\ ((oget res).`1 = Adv => (oget res).`2.`2 \\in  adv_pis_rf_info UC__RF.rf_info))].
proof.
apply (RFCore.MakeRF_invoke_term_metric_hoare (%s) %s.%s %s.%s).
apply %s.%s.
 qed.@]@;@;"
uc__rf (invarIRP rfbt true) real
uc__rf (metric_name_IRP rfbt true) real
uc__rf (invarIRP rfbt true) real
uc__rf (metric_name_IRP rfbt true) real
real uc__rf (invarIRP rfbt true) uc__rf (metric_name_IRP rfbt true)
    uc__rf (invokeIRP rfbt true);
    Format.fprintf ppf
"@[(* now we lift our invariant, termination metric and lemmas to
   RFRP *)@]@;@;";
    let range = get_MakeRFs_glob_range_of_real_fun_glob_core gvil in
    Format.fprintf ppf "@[%a@]@;@;"
    (print_glob_operator "glob_RFRP_to_Core" _RFRP real) range;
    Format.fprintf ppf
"@[op RFRP_invar : glob RFRP -> bool =
  fun (g : glob RFRP) => %s.%s (glob_RFRP_to_Core g).

op RFRP_metric : glob RFRP -> int =
  fun (g : glob RFRP) => %s.%s (glob_RFRP_to_Core g).

lemma RFRP_metric_good (g : glob RFRP) :
  RFRP_invar g => 0 <= RFRP_metric g.
    proof.
 smt(%s.%s). qed.
 "
uc__rf (invarIRP rfbt true)
uc__rf (metric_name_IRP rfbt true)
uc__rf (metric_goodIRP rfbt true);

Format.fprintf ppf 
"lemma RFRP_init_invar_hoare :
  hoare [RFRP.init : true ==> RFRP_invar (glob RFRP)].
proof.
rewrite /RFRP_invar /=.
apply RFRP_Core_init_invar_hoare.
qed.

lemma RFRP_invoke_term_metric_hoare (n : int) :
  hoare
  [RFRP.invoke :
   RFRP_invar (glob RFRP) /\\ RFRP_metric (glob RFRP) = n ==>
   RFRP_invar (glob RFRP) /\\
 (res <> None => RFRP_metric (glob RFRP) < n
 /\\ ((oget res).`1 = Adv => (oget res).`2.`2 \\in  adv_pis_rf_info UC__RF.rf_info))].
proof.
rewrite /RFRP_invar /RFRP_metric /=.
apply RFRP_Core_invoke_term_metric_hoare.
qed.@]@;@;"
  in
  print_cloneRF;
  print_MakeRF_and_lemmas

let print_party_state_metric
      (name : string) (type_name : string)
  (state_name : string -> string)
  (ppf : Format.formatter) (st_map : state_tyd IdMap.t) : unit =
  let lin = linearize_state_DAG st_map in
  match lin with
  | None -> Format.fprintf ppf
              "@[(*cannot generate operator %s, states have cycles*)@]" name
  | Some id_lvl_map ->
     begin
   
     Format.fprintf ppf
       "@[<v>@[op [smt_opaque] %s (g : %s) : int =@]@;<0 2>@[<v>"
       name type_name;
     Format.fprintf ppf "@[match g with@]@;";
     IdMap.iter (fun id lvl ->
         Format.fprintf ppf "@[| %s %a=> %i@]@;"
           (state_name id) (print_ctor_args_state_metric id) st_map lvl
       ) id_lvl_map;
     Format.fprintf ppf "@[end.@]@;@]@;@]"
     end

    
let print_RF_metric (id : string) (root : string)
      (mbmap : message_body_tyd SLMap.t) (dii : symb_pair IdMap.t)
      (gvil : gvil)
      (ppf : Format.formatter) (rfbt : real_fun_body_tyd)
    : unit =
  let parties = rfbt.parties in
  let ptns = fst (List.split (IdMap.bindings parties)) in
  let pmns = indexed_map_to_list_only_keep_keys rfbt.params in
  let rpmns = List.map (fun pmn -> (module_name pmn)^".RF") pmns in
  let ipmns = List.map (fun pmn -> (module_name pmn)^".IF") pmns in
  let sfns = fst (List.split (IdMap.bindings rfbt.sub_funs)) in
  let module_name = module_name id in
  let print_party_metric (pn : string) (pt : party_tyd) : unit =
    let metric_name = uc_party_metric_name pn in
    let st_map = (EcLocation.unloc pt).states in
    let snf = state_name_pt pn in
    let stn = state_type_name_pt pn in
    let svn = st_name pn in
    let invar_op_name = invar_pt_op_name pn in
    let svim = get_glob_indices_of_real_fun_parties rfbt gvil.gvil_RP in
    let lemma_pt_metric_good_name = _metric_pt_good pn in
    let print_Pt_lemma_metric_invoke (ppf : Format.formatter)
    (globop : string) : unit =
      let print_lemma_params ppf pmns =
        List.iter(fun pmn -> Format.fprintf ppf "@[(%s <: FUNC)@]@ " pmn) pmns
      in
      
      Format.fprintf ppf
        "@[lemma %s (n : int) %a : hoare [@]@;<0 2>@[<v>"
        (_invoke_pn pn) print_lemma_params pmns;
      Format.fprintf ppf
        "@[%s%s.%s :@ %s (%s(glob %s)) = n@ ==>@ (res <> None =>@ %s (%s(glob %s)) < n@]@;"
        module_name (module_params_string pmns) (proc_party_str pn)
        metric_name globop module_name
        metric_name globop module_name;
      Format.fprintf ppf
        "@[ /\\ ((oget res).`1 = %s => (oget res).`2.`2 \\in  adv_pis_rf_info %s))@]"
        mode_Adv rf_info;
      Format.fprintf ppf "@]@;].@;";
      Format.fprintf ppf
        "@[proof. rewrite /%s /=. proc. inline. (*inline procedure calls*)@]@;"
        metric_name;
      print_proof_state_match root mbmap dii "" ppf st_map;
      Format.fprintf ppf "@[qed.@]@;"
    in
    let print_party_metric_good ppf () =
      Format.fprintf ppf "@[lemma %s (g : %s) :@]@;"
        lemma_pt_metric_good_name stn;
      Format.fprintf ppf "@[  %s g => 0 <= %s g.@]@;" invar_op_name metric_name;
      Format.fprintf ppf "@[    proof. rewrite /%s /=.@]@;" metric_name;
      Format.fprintf ppf "@[      smt(). qed.@]@;";
    in
    let pt_glob_op_name =  glob_op_name module_name svn in
    let svi = IdMap.find pn svim in
    Format.fprintf ppf "@[op %s (g : glob %s) / : %s = g.`%i.@]@;@;"
      pt_glob_op_name module_name stn svi;
    Format.fprintf ppf "@[%a@]@;@;"
    (print_party_state_metric metric_name stn snf)
    st_map;
    Format.fprintf ppf
      "@[%a@]@;@;" print_Pt_lemma_metric_invoke pt_glob_op_name;
    Format.fprintf ppf "@[op %s (g : %s) : bool = predT g.@]@;@;"
      invar_op_name stn;
    Format.fprintf ppf
      "@[<v>%a@]@;@;"  print_party_metric_good ()
  in
  let print_module_abbrev (rp : bool) =
    let desc = if rp then "real" else "ideal" in
    let pmns = if rp then rpmns else ipmns in
    Format.fprintf ppf "@[(*abbreviation for module with %s parameters*)@]@;"
      desc;
    Format.fprintf ppf "@[module %s = %s.@]@;@;" 
      (moduleIRP id rfbt rp) (module_name^(module_params_string pmns))
  in
  let print_glob_operators (rp : bool) =
    let gvil = if rp then gvil.gvil_RP else gvil.gvil_IP in
    Format.fprintf ppf "@[%a@]@;@;"
      (print_glob_operator (glob_op_name_own (moduleIRP id rfbt rp))
         (moduleIRP id rfbt rp) module_name)
      (get_own_glob_range_of_real_fun_glob_core rfbt gvil);
    List.iter (fun pmn -> Format.fprintf ppf "@[%a@]@;@;"
      (print_glob_operator (glob_op_name (moduleIRP id rfbt rp) (uc_name pmn))
         (moduleIRP id rfbt rp) ((module_name_IRF rp) pmn))
      (get_glob_range_of_parameter gvil pmn)) pmns;
    let ogrs = get_own_glob_ranges_of_real_fun rfbt gvil in
    List.iter (fun sfn -> Format.fprintf ppf "@[%a@]@;@;"
      (print_glob_operator (glob_op_name (moduleIRP id rfbt rp) (uc_name sfn))
         module_name (module_name_IF sfn))
      (IdMap.find sfn ogrs)) sfns;
  in
  let print_metric_operator (rp : bool) =
    Format.fprintf ppf "@[<v>";
    Format.fprintf ppf "@[ op [smt_opaque] %s (g : glob %s) : int =@]@;"
      (metric_name_IRP rfbt rp) (moduleIRP id rfbt rp);
    let is_first = ref true in
    let plus() = if !is_first then begin is_first:=false; " " end else "+"
    in
    List.iter (fun pmn -> let ucpmn = uc_name pmn in
        Format.fprintf ppf "@[%s%s.%s(%s g)@]@;"
          (plus()) ucpmn (metricIRF rp) (glob_op_name (moduleIRP id rfbt rp) ucpmn)
      ) pmns;
    List.iter (fun ptn ->  Format.fprintf ppf "@[%s%s(%s (%s g))@]@;"
          (plus()) (uc_party_metric_name ptn)
          (glob_op_name module_name (st_name ptn))
          (glob_op_name_own (moduleIRP id rfbt rp))
    ) ptns;
    List.iter (fun sfn -> let ucsfn = uc_name sfn in
        Format.fprintf ppf "@[%s%s.%s(%s (%s g))@]@;"
          (plus()) ucsfn _metric_IF (glob_op_name (moduleIRP id rfbt rp) ucsfn)
          (glob_op_name_own (moduleIRP id rfbt rp))
    ) sfns;
    Format.fprintf ppf ".@]@;@;"
  in
  let print_invoke_lemma (rp : bool) =
    let print_call_sub_invoke metric globop1 globop2 sub_invoke sub_invoke_pms smt_hint =
      Format.fprintf ppf "@[  if.@]@;";
      Format.fprintf ppf "@[  exlim (%s(%s(%s(glob %s)))) => _sub_metric.@]@;"
        metric globop1 globop2 (moduleIRP id rfbt rp);
      Format.fprintf ppf "@[  call (%s _sub_metric %s).@]@;"
        sub_invoke sub_invoke_pms;
      Format.fprintf ppf "@[  skip.@]@;";
      Format.fprintf ppf "@[  smt(%s).@]@;" smt_hint;
    in
    Format.fprintf ppf "@[<v>";
    Format.fprintf ppf "@[lemma %s (n : int)  : hoare [@]@;" (invokeIRP rfbt rp);
    Format.fprintf ppf "@[  %s.%s :@]@;" (moduleIRP id rfbt rp) invoke;
    Format.fprintf ppf "@[  %s (glob %s) = n@]@;"
    (metric_name_IRP rfbt rp) (moduleIRP id rfbt rp);
    Format.fprintf ppf "@[  ==>@]@;";
    Format.fprintf ppf "@[  (res <> None =>@]@;";
    Format.fprintf ppf "@[  %s (glob %s) < n@]@;"
    (metric_name_IRP rfbt rp) (moduleIRP id rfbt rp);
    Format.fprintf ppf "@[/\\ ((oget res).`1 = Adv => (oget res).`2.`2 \\in  adv_pis_rf_info rf_info))].@]@;";
    Format.fprintf ppf "@[proof.@]@;";
    Format.fprintf ppf "@[rewrite /%s /=.@]@;" (metric_name_IRP rfbt rp);
    Format.fprintf ppf "@[  proc.@]@;";
    Format.fprintf ppf "@[  sp 1.@]@;";
    List.iter (fun sfn ->
        let ucsfn = uc_name sfn in
        let metric = ucsfn^"."^_metric_IF in
        let globop1 = glob_op_name (moduleIRP id rfbt rp) ucsfn in
        let globop2 = glob_op_name_own (moduleIRP id rfbt rp) in
        let sub_invoke = ucsfn^"."^_invoke_IF in
        let sub_invoke_pms = "" in
        print_call_sub_invoke metric globop1 globop2 sub_invoke sub_invoke_pms smt_sat_lemmas 
      ) sfns;
    List.iter (fun pmn ->
        let ucpmn = uc_name pmn in
        let metric = ucpmn^"."^(metricIRF rp) in
        let globop1 = glob_op_name (moduleIRP id rfbt rp) ucpmn in
        let globop2 = "" in
        let sub_invoke = ucpmn^"."^(invokeIRF rp) in
        let sub_invoke_pms = "" in
        print_call_sub_invoke metric globop1 globop2 sub_invoke sub_invoke_pms smt_sat_lemmas
      ) pmns;
    List.iter (fun ptn ->
        let pmns = if rp then rpmns else ipmns in
        let metric = uc_party_metric_name ptn in
        let globop1 = glob_op_name module_name (st_name ptn) in
        let globop2 = glob_op_name_own (moduleIRP id rfbt rp) in
        let sub_invoke = (_invoke_pn ptn) in
        let sub_invoke_pms = List.fold_left(fun acc pmn ->
          acc^" "^pmn)  "" pmns in
        print_call_sub_invoke metric globop1 globop2 sub_invoke sub_invoke_pms ""
      ) ptns;
    Format.fprintf ppf "@[  skip.@]@;";
    Format.fprintf ppf "@[  smt().@]@;";
    Format.fprintf ppf "qed.@]@;@;"
  in
  let print_invar_operator (rp : bool) =
    Format.fprintf ppf "@[<v>";
    Format.fprintf ppf "@[ op %s (g : glob %s) : bool =@]@;"
      (invarIRP rfbt rp) (moduleIRP id rfbt rp);
    let is_first = ref true in
    let cnj() = if !is_first then begin is_first:=false; "  " end else "/\\"
    in
    List.iter (fun pmn -> let ucpmn = uc_name pmn in
        Format.fprintf ppf "@[%s%s.%s(%s g)@]@;"
          (cnj()) ucpmn (invarIRF rp)
          (glob_op_name (moduleIRP id rfbt rp) ucpmn)
      ) pmns;
    List.iter (fun ptn ->  Format.fprintf ppf "@[%s%s(%s (%s g))@]@;"
          (cnj()) (invar_pt_op_name ptn)
          (glob_op_name module_name (st_name ptn))
          (glob_op_name_own (moduleIRP id rfbt rp))
    ) ptns;
    List.iter (fun sfn -> let ucsfn = uc_name sfn in
        Format.fprintf ppf "@[%s%s.%s(%s (%s g))@]@;"
          (cnj()) ucsfn _invar_IF
          (glob_op_name (moduleIRP id rfbt rp) ucsfn)
          (glob_op_name_own (moduleIRP id rfbt rp))
    ) sfns;
    Format.fprintf ppf ".@]@;@;"
  in
  let print_metric_good_lemma (rp : bool) =
    Format.fprintf ppf "@[<v>";
    Format.fprintf ppf "@[lemma %s (g : glob %s) :@]@;"
    (metric_goodIRP rfbt rp) (moduleIRP id rfbt rp);
    Format.fprintf ppf "@[%s g => 0 <= %s g.@]@;"
      (invarIRP rfbt rp) (metric_name_IRP rfbt rp);
    Format.fprintf ppf "@[proof.@]@;";
    Format.fprintf ppf "@[rewrite /%s /=.@]@;"
      (metric_name_IRP rfbt rp);
    Format.fprintf ppf "@[rewrite /%s /=.@]@;"
      (invarIRP rfbt rp);
    Format.fprintf ppf "@[smt(@]@;";
    List.iter(fun pmn ->
        Format.fprintf ppf "@[%s.%s@]@;"
          (uc_name pmn) (metric_goodIRF rp)
      ) pmns;
    List.iter(fun sfn ->
        Format.fprintf ppf "@[%s.%s@]@;" (uc_name sfn) _metric_good_IF
      ) sfns;
    List.iter(fun ptn ->
        Format.fprintf ppf "@[%s@]@;" (_metric_pt_good ptn)
      ) ptns;
    Format.fprintf ppf "@[).@]@;";
    Format.fprintf ppf "qed.@]@;@;"
  in
  let print_init_lemma (rp : bool) =
    Format.fprintf ppf "@[<v>";
    Format.fprintf ppf "@[lemma %s :@]@;" (initIRP rfbt rp);
    Format.fprintf ppf "@[hoare [ %s.%s : true ==> %s (glob %s)].@]@;"
      (moduleIRP id rfbt rp) init
      (invarIRP rfbt rp) (moduleIRP id rfbt rp);
    Format.fprintf ppf "@[proof. proc. sp. wp.@]@;";
    List.iter(fun pmn ->
        Format.fprintf ppf "@[call (%s.%s).@]@;"
          (uc_name pmn) (initIRF rp)
      ) (List.rev pmns);
    List.iter(fun sfn ->
        Format.fprintf ppf "@[call (%s.%s).@]@;"
          (uc_name sfn) _init_IF
      ) (List.rev sfns);
    Format.fprintf ppf "@[skip.@]@;";
    Format.fprintf ppf "@[rewrite /%s /=.@]@;"
      (invarIRP rfbt rp);
    Format.fprintf ppf "@[smt().@]@;";
    Format.fprintf ppf "qed.@]@;@;"
  in
  let parties = IdMap.bindings parties in
  let parties = List.rev parties in
  List.iter (fun (pn,pt) -> print_party_metric pn pt) parties;
  let print_it (rp : bool) =
    print_glob_operators (rp);
    print_metric_operator (rp);
    print_invoke_lemma (rp);
    print_invar_operator(rp);
    print_metric_good_lemma(rp);
    print_init_lemma (rp)
  in
  if IdMap.is_empty rfbt.params
  then print_it true
  else begin
      print_module_abbrev true;
      print_it true;
      print_module_abbrev false;
      print_it false;
  end
  


let gen_real_fun (sc : EcScope.scope) (root : string) (id : string)
      (mbmap : message_body_tyd SLMap.t) (rfbt : real_fun_body_tyd)
      (rapm : rf_addr_port_maps)
      (dii : symb_pair IdMap.t) (gvil : gvil) : string =
  let sf = Format.get_str_formatter () in
  Format.fprintf sf "@[<v>";
  Format.fprintf sf "@[%s@]@;@;" (open_theory uc__rf);
  Format.fprintf sf "@[%a@]@;@;" print_rf_info_operator rfbt;
  Format.fprintf sf "@[%a@]@;@;" (print_addr_and_port_operators sc) rapm;
  Format.fprintf sf "@[%a@]@;@;" (print_party_types sc) rfbt.parties;
  Format.fprintf sf "@[%a@]@;@;" (print_real_module sc root id mbmap dii
                                    rapm.party_ext_port_id) rfbt;
  Format.fprintf sf "@[<v>%a@]@;@;"
    (print_RF_metric id root mbmap dii gvil) rfbt;
  for i = 1 to IdMap.cardinal rfbt.params do
    Format.fprintf sf "@[%a@]@;@;"
     (print_rest_module sc root id mbmap dii rapm.party_ext_port_id rfbt) i
  done;
  Format.fprintf sf "@[%s@]@;@;" (close_theory uc__rf);
  Format.fprintf sf "@[<v>%a@]@;@;"   print_cloneRF_MakeRF (id,rfbt, gvil.gvil_RP);
  Format.fprintf sf "@]";
  Format.flush_str_formatter ()

let gen_fun (sc : EcScope.scope) (root : string) (id : string)
      (mbmap : message_body_tyd SLMap.t)
      (rapm : rf_addr_port_maps option) (ft : fun_tyd) (dii : symb_pair IdMap.t)
      (gvil : gvil) : string =
  let fbt = EcLocation.unloc ft in
  match fbt with
  | FunBodyIdealTyd ifbt -> gen_ideal_fun sc root id mbmap ifbt dii
  | FunBodyRealTyd rfbt  -> gen_real_fun sc root id mbmap rfbt (EcUtils.oget rapm) dii gvil

let print_simulator_module (sc : EcScope.scope) (root : string) (id : string)
  (mbmap : message_body_tyd SLMap.t) (dii : symb_pair IdMap.t)
  (ais : symb_pair IdPairMap.t) (ppf : Format.formatter) (sbt : sim_body_tyd)
    : unit =
  let print_vars () =
    Format.fprintf ppf "@[var %s : %a option@]@;"
      if_addr_opt (pp_type sc) addr_ty;
     Format.fprintf ppf "@[var %s : %s@]@;" _st state_type_name_IF;
  in
  let print_proc_init () =
    Format.fprintf ppf "@[proc init() : unit = {@]@;<0 2>@[<v>";
    Format.fprintf ppf "@[%s <- None; %s <- %s;@]@;"
      if_addr_opt _st (state_name (initial_state_id_of_states sbt.states));
    Format.fprintf ppf "@[%s.init();@]@]@;@[}@]@;" _Adv
  in
  
  let print_state_match_branch (stid : string)
        (ppf : Format.formatter) (st : state_tyd)
      : unit =
  let st = EcLocation.unloc st in
  let spnt = sparams_map_to_list st.params in
  let print_state_params_names ppf spnt =
    List.iter (fun (n,_) -> Format.fprintf ppf "%s@ " n) spnt
  in
  let rec print_mm ppf (mmcs : msg_match_clause_tyd list) : unit =
    let print_mm_guard ppf (mp : msg_path) : unit =
      let iip = (EcLocation.unloc mp).inter_id_path in
      let is_from_IF iip : bool =
        (List.hd iip) = sbt.uses
      in
      let is_for_Party iip : string option =
        let sims = List.hd iip in
        let ptnm = List.hd (List.tl iip) in
        let sim_key = (sims,ptnm) in
        if (sims = sbt.sims) && (IdPairMap.mem sim_key ais) &&
             ptnm = snd (IdPairMap.find sim_key ais)
        then Some ptnm
        else None
      in
      let is_for_sf_pm iip : string option =
        let sims = List.hd iip in
        let sfpmnm = List.hd (List.tl iip) in
        if IdPairMap.mem (sims,sfpmnm) ais
        then Some sfpmnm
        else None
      in
      
      if is_from_IF iip
      then Format.fprintf ppf "(%s.`3.`1 = %s) /\\ (%s.`2.`1 = adv)"
             _m oget_if_addr_opt _m
      else
        if (is_for_Party iip) <> None
        then
          Format.fprintf ppf "(%s.`3.`1 = adv) /\\ (%s.`2.`1 = %s)"
            _m _m oget_if_addr_opt
        else
          if (is_for_sf_pm iip) <> None
          then
            let nm = EcUtils.oget (is_for_sf_pm iip) in
            Format.fprintf ppf "(%s.`3.`1 = adv) /\\ (%s.`2.`1 = %s)"
              _m _m (addr_op_call_sim nm)
          else UcMessage.failure "incomming messages for simulator should be from IF or to parties, parameters or sub-functionalities of simulated RF"
    in
    if List.is_empty mmcs
    then ()
    else
      let mmc = List.hd mmcs in
      let mp = get_msg_path mmc.msg_pat.msg_path_pat in
      let msg_name, is_internal, iiphd, pfx, mb, epdp_str =
        get_msg_info mp IdMap.empty ais root mbmap in
      Format.fprintf ppf "@[if (%a /\\ (%s.`dec %s) <> None)@]@;"
        print_mm_guard mp epdp_str _m;
      Format.fprintf ppf "@[{@]@;<0 2>@[<v>";
      let objstr = "(oget ("^epdp_str^".`dec "^_m^"))" in
      print_mmc_proc_call ~objstr
        ppf stid st.params mmc pfx msg_name mb state_name "";
      Format.fprintf ppf "@]@;}@;";
      if List.is_empty (List.tl mmcs)
      then ()
      else begin
          Format.fprintf ppf "@[else {@]@;<0 2>@[<v>";
          print_mm ppf (List.tl mmcs);
          Format.fprintf ppf "@]@;}@;"
        end
  in
  let mmcs = List.filter (fun mmc -> not
    (UcSpecTypedSpecCommon.msg_path_pat_ends_star mmc.msg_pat.msg_path_pat)
  ) st.mmclauses in
  Format.fprintf ppf "@[| %s %a=> {@]@;<0 2>@[<v>"
    (state_name stid) print_state_params_names spnt;
  print_mm ppf mmcs;
  Format.fprintf ppf "@]@;}@;"
  in

  let print_proc_invoke 
      (ppf : Format.formatter) (states : state_tyd IdMap.t) : unit =
    Format.fprintf ppf "@[proc invoke(%s : %a) : %a option = {@]@;<0 2>@[<v>"
    _m (pp_type sc) msg_ty (pp_type sc) msg_ty;
    Format.fprintf ppf "@[var %s : %a option <- None;@]@;"
      _r (pp_type sc) msg_ty;
    Format.fprintf ppf "@[if (%s = None) {%s <- Some %s.`3.`1;}@]@;"
      if_addr_opt if_addr_opt _m;
    Format.fprintf ppf "@[match %s with@]@;" _st;
    IdMap.iter (fun stid st -> Format.fprintf ppf "%a"
      (print_state_match_branch stid) st) states;
    Format.fprintf ppf "@[end;@]@;";
    Format.fprintf ppf "@[return %s;@]" _r;
    Format.fprintf ppf "@]@;}@;"
  in
  Format.fprintf ppf "@[module %s (%s : ADV)= {@]@;<0 2>@[<v>"
    (uc_name id) _Adv;
  print_vars ();
  print_proc_init ();
  let sim_uses = Some sbt.uses in
  print_mmc_procs ~sim_uses
    sc root mbmap ppf sbt.states state_name dii ais None "";
  print_proc_invoke ppf sbt.states;
  Format.fprintf ppf "@]@\n}.";
  ()
  
let print_cloneSIM_MS ppf (id,sbt : string * sim_body_tyd) =
  let print_cloneSIM =
  Format.fprintf ppf "@;@[clone MakeSimulator as MSCore with@]@;";
  Format.fprintf ppf "@[op core_pi <- %s@]@;" adv_if_pi_op_name;
  Format.fprintf ppf "@[proof *.@]@;";
  Format.fprintf ppf "@[realize core_pi_gt0. smt(%s). qed.@]@;"
    adv_pi_begin_gt0_axiom_name
  in 
  let print_MS =
    Format.fprintf ppf
      "@[module SIM(%s : ADV) = MSCore.MS(%s.%s(%s), %s).@]"
      _Adv uc__sim (uc_name id) _Adv _Adv
  in
  print_cloneSIM;
  print_MS

let gen_sim (sc : EcScope.scope) (root : string) (id : string)
      (mbmap : message_body_tyd SLMap.t) (sbt : sim_body_tyd)
      (ais : symb_pair IdPairMap.t): string =
  let sf = Format.get_str_formatter () in
  Format.fprintf sf "@[<v>";
  Format.fprintf sf "@[%s@]@;@;" (open_theory uc__sim);
  Format.fprintf sf "@[%a@]@;@;" (print_state_type_IF sc) sbt.states;
  Format.fprintf sf "@[%a@]@;@;"
    (print_simulator_module sc root id mbmap IdMap.empty ais) sbt;
  Format.fprintf sf "@[%s@]@;" (close_theory uc__sim);
  Format.fprintf sf "@[<v>%a@]@;"   print_cloneSIM_MS (id,sbt);
  Format.fprintf sf "@]";
  Format.flush_str_formatter ()


open UcTypedSpec
open UcSpecTypedSpecCommon
open EcTypes
open UcGenerateCommon

let state_name_IF (name : string) : string = "_State_"^name
let state_type_name_IF = "_state"

let state_name_pt (ptname : string) (sname : string) : string =
  "_State_"^ptname^"_"^sname
let state_type_name_pt (ptname : string) : string =
  "_state_"^ptname

let uc__if = "UC__IF"
let uc__rf = "UC__RF"
let uc__sim = "UC__SIM"
let _st = "_st"
let st_name (name : string) = "_st_"^name
let _m = "_m"
let _r = "_r"
let _x = "_x"
let _envport = "envport"
let msg_ty : ty =
  tconstr (EcPath.fromqsymbol (uc_qsym_prefix_basic_types, "msg")) []
let parties_str = "parties"
let loop_str = "loop"
let proc_party_str (pn : string) = "party_"^pn

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
  print_state_type sc ppf states state_type_name_IF state_name_IF 

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
  mmc_proc_name stid mpp state_name_IF

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

let qual_epdp_name (msgn : string) (pfx : string)
    : string =
  let _mty_name = msg_ty_name msgn in
  let _epdp_op_name = epdp_op_name _mty_name in
  pfx^_epdp_op_name
  
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

let get_msg_info (mp : msg_path) (dii : symb_pair IdMap.t) (root : string)
      (mbmap : message_body_tyd SLMap.t)
    : string * bool * string * string * message_body_tyd * string =
    let msg_path = EcLocation.unloc mp in
    let msgn = msg_path.msg in
    let iiphd = List.hd msg_path.inter_id_path in
    let is_internal = IdMap.mem iiphd dii in
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
        let iip = msg_path.inter_id_path in
        let loc,mb = get_msg_body mbmap root iip msgn in
        let pfx = inter_id_path_str loc iip in
        pfx, mb
    in
    let epdp_str = qual_epdp_name msgn pfx in
    msgn, is_internal, iiphd, pfx, mb, epdp_str
  
let rec print_code (sc :  EcScope.scope) (root : string)
          (mbmap : message_body_tyd SLMap.t)(ppf : Format.formatter)
          (code : instruction_tyd list EcLocation.located)
          (state_name : string -> string) (dii : symb_pair IdMap.t)
          (ptn : string option)
          (intprts : EcIdent.t QidMap.t) : unit =
  let pp_ex = pp_expr ~intprts:intprts sc in
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
    print_code sc root mbmap ppf thencode state_name dii ptn intprts;
    Format.fprintf ppf  "@]@;}";
    match elsecodeo with
    | Some code ->
      Format.fprintf ppf "@;@[else {@]@;<0 2>@[<v>";
      print_code sc root mbmap ppf code state_name dii ptn intprts; 
      Format.fprintf ppf  "@]@;}"
    | None -> ()
  in
  let print_sat_instr (sat : send_and_transition_tyd) : unit =
    (*send part*)
    let msgn, is_internal, iiphd, pfx, mb, epdp_str =
      get_msg_info sat.msg_expr.path dii root mbmap in
    if not is_internal then
    begin match mb.port with
    | Some port ->
       Format.fprintf ppf
         "@[if (%s %s %s) {@]@;<0 2>@[<v>"
         _envport _self port
    | None -> ()
    end
    else ()
    ;
    Format.fprintf ppf "@[%s <- Some@]@;<0 2>@[<v>(%s.`enc@;"
      _r epdp_str;
    Format.fprintf ppf "{|@;<0 2>@[<v>";

    if is_internal
    then
      Format.fprintf ppf "@[%s%s = %s;@]@;"
      pfx (name_record_func msgn) (addr_op_call iiphd)
    else    
    Format.fprintf ppf "@[%s%s = %s;@]@;"
      pfx (name_record_func msgn) _self
    ;
    begin match mb.port with
    | Some _ ->
       if is_internal
       then
         Format.fprintf ppf "@[%s%s = %s;@]@;"
           pfx (name_record_dir_port msgn mb) (intport_op_call (EcUtils.oget ptn))
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
    Format.fprintf ppf "@[%s <- %s"
      state_var_name (state_name (EcLocation.unloc sat.state_expr.id));
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
      print_code sc root mbmap ppf codeblock state_name dii ptn intprts; 
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
  

let print_mmc_proc (sc : EcScope.scope) (root : string)
      (mbmap : message_body_tyd SLMap.t) (ppf : Format.formatter)
      (state_id : string) (params : ty_index Mid.t)
      (vars : (EcIdent.t * ty) EcLocation.located IdMap.t)
      (mmc : msg_match_clause_tyd) (state_name : string -> string)
      (dii : symb_pair IdMap.t) (ptn : string option)
    (intprts : EcIdent.t QidMap.t) : unit =
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
  print_code sc root mbmap ppf mmc.code state_name dii ptn intprts;
  Format.fprintf ppf "@[return %s;@]" _r;
  Format.fprintf ppf "@]@;}@;"

let print_mmc_procs (sc : EcScope.scope) (root : string)
      (mbmap : message_body_tyd SLMap.t) (ppf : Format.formatter)
      (states : state_tyd IdMap.t) (state_name : string -> string)
      (dii : symb_pair IdMap.t) (ptn : string option) : unit =
  IdMap.iter(fun id st -> let st:state_body_tyd = EcLocation.unloc st in
    List.iter(fun mmc ->
      if UcSpecTypedSpecCommon.msg_path_pat_ends_star mmc.msg_pat.msg_path_pat
      then ()
      else print_mmc_proc sc root mbmap ppf id st.params st.vars mmc state_name dii ptn st.internal_ports
      ;) st.mmclauses
    ) states

let print_mmc_proc_call (ppf : Format.formatter)
      (state_id : string) (params : ty_index Mid.t) (mmc : msg_match_clause_tyd)
      (pfx : string) (msgn : string) (mb : message_body_tyd)
      (state_name : string -> string) : unit =
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
    let pfx = _x^".`"^pfx in
    List.map (fun r -> pfx^r) records
  in
  let params_list = fst (List.split (sparams_map_to_list params)) in
  let params_list = params_list @ (mmc_msg_pat_bindings mmc) in
  Format.fprintf ppf "@[%s %s %s (%a);@]"
    _r "<@" (mmc_proc_name state_id mmc.msg_pat.msg_path_pat state_name)
    print_proc_params_call params_list


let print_state_match_branch (root : string) (id : string)
      (mbmap : message_body_tyd SLMap.t) (state_name : string -> string)
(dii : symb_pair IdMap.t) (ppf : Format.formatter) (st : state_tyd) : unit =
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
        get_msg_info mp dii root mbmap in
      Format.fprintf ppf "@[match %s.`dec %s with@]@;"
        epdp_str _m;
      Format.fprintf ppf "@[| Some %s => {@]@;<0 2>@[<v>" _x;
      print_mmc_proc_call ppf id st.params mmc pfx msg_name mb state_name;
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
      (ppf : Format.formatter) (states : state_tyd IdMap.t)
      (pno : string option) : unit =
  Format.fprintf ppf "@[proc %s(%s : %a) : %a option = {@]@;<0 2>@[<v>"
    procn _m (pp_type sc) msg_ty (pp_type sc) msg_ty;
    Format.fprintf ppf "@[var %s : %a option <- None;@]@;"
      _r (pp_type sc) msg_ty;
    let state_var_name =
      match pno with
      | None -> _st
      | Some pn -> st_name pn in
    Format.fprintf ppf "@[match %s with@]@;" state_var_name;
    IdMap.iter (fun id st -> Format.fprintf ppf "%a"
      (print_state_match_branch root id mbmap state_name dii) st) states;
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
    _self _st (state_name_IF (initial_state_id_of_states ifbt.states));
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
    Format.fprintf ppf "@[proc invoke(%s : %a) : %a option = {@]@;<0 2>@[<v>"
      m (pp_type sc) msg_ty (pp_type sc) msg_ty;
    Format.fprintf ppf "@[var %s : %a option <- None;@]@;"
      r (pp_type sc) msg_ty;
    Format.fprintf ppf
      "@[if ((%s.`1 = %s@ /\\@ %s.`2.`1 = %s@ /\\@ (%a)@ /\\@ envport %s %s.`3)@]"
         m mode_Dir m _self print_dir_pi_guard()  _self m;
     Format.fprintf ppf "\\/";
     Format.fprintf ppf
       "@[@ (%s.`1 = %s@ /\\@ %s.`2.`1 = %s@ /\\@ %s.`2.`2 = %s.pi@ /\\@ %s.`3.`1 = %s))@]{"
          m mode_Adv m _self m (uc_name ifbt.id_adv_inter) m adv;
    Format.fprintf ppf "@;<0 2>@[%s %s %s(%s);@]" r "<@" parties_str m;
    Format.fprintf ppf "@;}@]@;@[return %s;@]@;}@;" r
  in

  Format.fprintf ppf "@[module %s : FUNC= {@]@;<0 2>@[<v>" (uc_name id);
  print_vars ();
  print_proc_init ();
  print_mmc_procs sc root mbmap ppf ifbt.states state_name_IF dii None;
  print_proc_parties sc root id mbmap parties_str state_name_IF dii ppf ifbt.states None;
  print_proc_invoke ();
  Format.fprintf ppf "@]@\n}.";
  ()
  

let gen_ideal_fun (sc : EcScope.scope) (root : string) (id : string)
      (mbmap : message_body_tyd SLMap.t) (ifbt : ideal_fun_body_tyd)
      (dii : symb_pair IdMap.t) : string =
  let sf = Format.get_str_formatter () in
  Format.fprintf sf "@[<v>";
  Format.fprintf sf "@[%s@]@;@;" (open_theory uc__if);
  Format.fprintf sf "@[%a@]@;@;" (print_state_type_IF sc) ifbt.states;
  Format.fprintf sf "@[%a@]@;@;" (print_ideal_module sc root id mbmap dii) ifbt;
  Format.fprintf sf "@[%s@]@;" (close_theory uc__if);
  Format.fprintf sf "@]";
  Format.flush_str_formatter ()

let print_sub_fun_clones (ppf : Format.formatter)
      (rfbt : real_fun_body_tyd) : unit =
  let nsf = IdMap.cardinal rfbt.sub_funs in
  let bndgs = IdMap.bindings rfbt.sub_funs in
  for n = 0 to nsf-1 do
    let isf_name, (root, _) = List.nth bndgs n in
    clone_singleton_unit
      ppf root (uc_name isf_name) (adv_sf_pi_op_name isf_name)
  done

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
    print_extport_op pn n) rapm.party_ext_port_id;
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
    

let print_real_module (sc : EcScope.scope) (root : string) (id : string)
      (mbmap : message_body_tyd SLMap.t) (dii : symb_pair IdMap.t)
      (ppf : Format.formatter) (rfbt : real_fun_body_tyd) : unit =
  let print_vars () =
     Format.fprintf ppf "@[var %s : %a@]@;" _self (pp_type sc) addr_ty;
     IdMap.iter (fun pn _ ->
         Format.fprintf ppf "@[var %s : %s@]@;"
           (st_name pn) (state_type_name_pt pn)  
       ) rfbt.parties;
     Format.fprintf ppf "@;"
  in
  let subfunpath sfn sfid = (uc_name sfn)^"."^uc__code^"."^uc__if^"."^(uc_name sfid) in
  let print_proc_init () =
    Format.fprintf ppf "@[proc init(self_ : %a) : unit = {@]@;<0 2>"
    (pp_type sc) addr_ty;
    Format.fprintf ppf "@[%s <- self_;@]@;" _self;
    IdMap.iter (fun sfn (sfr, sfid) ->
      Format.fprintf ppf "@[%s.init(%s);@]@;"
        (subfunpath sfn sfid) (addr_op_call sfn)) rfbt.sub_funs;
    IdMap.iter (fun pn _ ->
      Format.fprintf ppf "@[%s.init(%s);@]@;"
       pn (addr_op_call pn)) rfbt.params;
    IdMap.iter (fun pn pt ->
    Format.fprintf ppf "@[ %s <- %s;@]@;"
      (st_name pn) (state_name_pt pn (initial_state_id_of_party_tyd  pt))
      ) rfbt.parties;
    Format.fprintf ppf "@[}@]@;"
  in
  let print_proc_invoke () =
    let r, m = "r", "m" in
    let print_subfun_or_param_invoke ppf (nm : string) (path : string): unit =
      Format.fprintf ppf
      "@[if@ (%s <= %s.`2.`1)@ {%s %s %s.invoke(%s);}@]@;"
         (addr_op_call nm) m r "<@" path m
    in
    let print_party_invoke ppf (nm : string) : unit =
      Format.fprintf ppf
      "@[if ((%s.`1 = %s@ /\\@ %s.`2 = %s@ /\\@ envport %s %s.`3)@]@;"
         m mode_Dir m (extport_op_call nm) _self m;
      Format.fprintf ppf "@[\\/@]@;";
      Format.fprintf ppf
        "@[(%s.`1 = %s@ /\\@ %s.`2 = %s@ /\\@ %s.`3.`1 = %s)@]@;"
        m mode_Adv m (extport_op_call nm) m adv;
      Format.fprintf ppf "@[\\/@]@;";
      Format.fprintf ppf
      "@[(%s.`1 = %s@ /\\@ %s.`2 = %s@ /\\@ %s <= %s.`3.`1))@]@;"
         m mode_Dir m (intport_op_call nm) _self m;
      Format.fprintf ppf "@[{%s %s %s(%s);}@]@;"
        r "<@" (proc_party_str nm) m
    in

    Format.fprintf ppf "@[proc invoke(%s : %a) : %a option = {@]@;<0 2>@[<v>"
      m (pp_type sc) msg_ty (pp_type sc) msg_ty;
    Format.fprintf ppf "@[var %s : %a option <- None;@]@;"
      r (pp_type sc) msg_ty;
    IdMap.iter (fun sfn (_,sfid) ->
        print_subfun_or_param_invoke ppf sfn (subfunpath sfn sfid)
      ) rfbt.sub_funs;
    IdMap.iter (fun pn _ ->
        print_subfun_or_param_invoke ppf pn pn) rfbt.params;
    IdMap.iter (fun pn _ ->
      print_party_invoke ppf pn) rfbt.parties;
    Format.fprintf ppf "@[return %s;@]@;}@;" r
  in

  Format.fprintf ppf "@[module %s %a : FUNC = {@]@;<0 2>@[<v>"
    (uc_name id) print_params_FUNC rfbt.params;
  print_vars ();
  print_proc_init ();
  IdMap.iter (fun (pn : string) (pt : party_tyd) ->
      let states = (EcLocation.unloc pt).states in
      let sn = (state_name_pt pn) in
      let ps = proc_party_str pn in
      print_mmc_procs sc root mbmap ppf states sn dii (Some pn);
      print_proc_parties sc root id mbmap ps sn dii ppf states (Some pn)
  ) rfbt.parties;
  print_proc_invoke ();
  Format.fprintf ppf "@]@\n}.";
  ()

let print_cloneRF_MakeRF ppf (id,rfbt : string * real_fun_body_tyd) =
  let print_cloneRF =
  Format.fprintf ppf "@;@[clone RealFunctionality as RFCore with@]@;";
  Format.fprintf ppf "@[op num_parties <- %i,@]@;"
    (IdMap.cardinal rfbt.parties);
  Format.fprintf ppf "@[op num_subfuns <- %i,@]@;"
    (IdMap.cardinal rfbt.sub_funs);
  Format.fprintf ppf "@[op num_params <- %i,@]@;"
    (IdMap.cardinal rfbt.params);
  Format.fprintf ppf "@[op adv_pi_num <- %s - 1,@]@;" adv_pi_num_op_name;
  Format.fprintf ppf "@[op adv_pi_begin <- %s + 1@]@;" adv_pi_begin_op_name;
  Format.fprintf ppf "@[proof *.@]@;";
  Format.fprintf ppf "@[realize ge1_num_parties. smt. qed.@]@;";
  Format.fprintf ppf "@[realize ge0_num_subfuns. smt. qed.@]@;";
  Format.fprintf ppf "@[realize ge0_num_params. smt. qed.@]@;";
  Format.fprintf ppf "@[realize ge0_adv_pi_num. smt. qed.@]@;";
  Format.fprintf ppf "@[realize ge1_adv_pi_begin. smt. qed.@]@;@;"
  in 
  let print_MakeRF =
    Format.fprintf ppf
    "@[module RF%a = RFCore.MakeRF(%s.%s%a).@]"
    print_params_FUNC rfbt.params
    uc__rf
    (uc_name id)
    print_params_list rfbt.params
  in
  print_cloneRF;
  print_MakeRF
    


let gen_real_fun (sc : EcScope.scope) (root : string) (id : string)
      (mbmap : message_body_tyd SLMap.t) (rfbt : real_fun_body_tyd) (rapm : rf_addr_port_maps)
      (dii : symb_pair IdMap.t) : string =
  let sf = Format.get_str_formatter () in
  Format.fprintf sf "@[<v>";
  Format.fprintf sf "@[%s@]@;@;" (open_theory uc__rf);
  Format.fprintf sf "@[%a@]@;@;" print_sub_fun_clones rfbt;
  Format.fprintf sf "@[%a@]@;@;" (print_addr_and_port_operators sc) rapm;
  Format.fprintf sf "@[%a@]@;@;" (print_party_types sc) rfbt.parties;
  Format.fprintf sf "@[%a@]@;@;" (print_real_module sc root id mbmap dii) rfbt;
  Format.fprintf sf "@[%s@]@;@;" (close_theory uc__rf);
  Format.fprintf sf "@[<v>%a@]@;"   print_cloneRF_MakeRF (id,rfbt);
  Format.fprintf sf "@]";
  Format.flush_str_formatter ()

let gen_fun (sc : EcScope.scope) (root : string) (id : string) (mbmap : message_body_tyd SLMap.t)
      (rapm : rf_addr_port_maps option) (ft : fun_tyd) (dii : symb_pair IdMap.t)
    : string =
  let fbt = EcLocation.unloc ft in
  match fbt with
  | FunBodyIdealTyd ifbt -> gen_ideal_fun sc root id mbmap ifbt dii
  | FunBodyRealTyd rfbt  -> gen_real_fun sc root id mbmap rfbt (EcUtils.oget rapm) dii 

let print_simulator_module (sc : EcScope.scope) (root : string) (id : string)
      (mbmap : message_body_tyd SLMap.t) (dii : symb_pair IdMap.t)
      (ppf : Format.formatter) (sbt : sim_body_tyd) : unit =
  let print_vars () =
     Format.fprintf ppf "@[var %s : %a@]@;" _self (pp_type sc) addr_ty;
     Format.fprintf ppf "@[var %s : %s@]@;" _st state_type_name_IF;
  in
  let print_proc_init () =
    Format.fprintf ppf "@[proc init(self_ : %a) : unit = {@]@;<0 2>"
    (pp_type sc) addr_ty;
    Format.fprintf ppf "@[%s <- self_; %s <- %s;@]@;@[}@]@;"
    _self _st (state_name_IF (initial_state_id_of_states sbt.states));
  in
  let print_proc_invoke () =
    let r, m = "r", "m" in
    Format.fprintf ppf "@[proc invoke(%s : %a) : %a option = {@]@;<0 2>@[<v>"
      m (pp_type sc) msg_ty (pp_type sc) msg_ty;
    Format.fprintf ppf "@[var %s : %a option <- None;@]@;"
      r (pp_type sc) msg_ty;
     Format.fprintf ppf
       "@[@ (%s.`1 = %s@ /\\@ %s.`2.`1 = %s@]{"
          m mode_Adv m _self;
    Format.fprintf ppf "@;<0 2>@[%s %s %s(%s);@]" r "<@" loop_str m;
    Format.fprintf ppf "@;}@]@;@[return %s;@]@;}@;" r
  in

  Format.fprintf ppf "@[module %s (%s : FUNC)= {@]@;<0 2>@[<v>"
    (uc_name id) _Adv;
  print_vars ();
  print_proc_init ();
  print_mmc_procs sc root mbmap ppf sbt.states state_name_IF dii None;
  print_proc_parties sc root id mbmap loop_str state_name_IF dii ppf sbt.states None;
  print_proc_invoke ();
  Format.fprintf ppf "@]@\n}.";
  ()
  

let gen_sim (sc : EcScope.scope) (root : string) (id : string)
      (mbmap : message_body_tyd SLMap.t) (sbt : sim_body_tyd) : string =
  let sf = Format.get_str_formatter () in
  Format.fprintf sf "@[<v>";
  Format.fprintf sf "@[%s@]@;@;" (open_theory uc__sim);
  Format.fprintf sf "@[%a@]@;@;" (print_state_type_IF sc) sbt.states;
  Format.fprintf sf "@[%a@]@;@;"
    (print_simulator_module sc root id mbmap IdMap.empty) sbt;
  Format.fprintf sf "@[%s@]@;" (close_theory uc__sim);
  Format.fprintf sf "@]";
  Format.flush_str_formatter ()


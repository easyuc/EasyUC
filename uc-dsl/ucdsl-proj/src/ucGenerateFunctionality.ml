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
let uc__code = "UC__Code"
let _st = "_st"
let st_name (name : string) = "_st_"^name
let _m = "_m"
let _r = "_r"
let _x = "_x"
let _envport = "envport"
let msg_ty : ty =
  tconstr (EcPath.fromqsymbol (uc_qsym_prefix_basic_types, "msg")) []

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

let qual_epdp_name (loc : bool) (msgn : string) (iid : string list)
    : string =
  let _mty_name = msg_ty_name msgn in
  let _epdp_op_name = epdp_op_name _mty_name in
  (inter_id_path_str loc iid)^_epdp_op_name
  
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

let rec print_code (sc :  EcScope.scope) (root : string)
          (mbmap : message_body_tyd SLMap.t)(ppf : Format.formatter)
          (code : instruction_tyd list EcLocation.located)
        (state_name : string -> string): unit =
  let print_fail_instr () : unit =
    Format.fprintf ppf "@[%s <- None;@]" _r
  in
  let print_ite_instr expr thencode elsecodeo : unit =
    Format.fprintf ppf "@[if (%a) {@]@;<0 2>@[<v>" (pp_expr sc) expr;
    print_code sc root mbmap ppf thencode state_name;
    Format.fprintf ppf  "@]@;}";
    match elsecodeo with
    | Some code ->
      Format.fprintf ppf "@;@[else {@]@;<0 2>@[<v>";
      print_code sc root mbmap ppf code state_name; 
      Format.fprintf ppf  "@]@;}"
    | None -> ()
  in
  let print_sat_instr (sat : send_and_transition_tyd) : unit =
    (*send part*)
    let msg_path = EcLocation.unloc sat.msg_expr.path in
    let iip = msg_path.inter_id_path in
    let msgn = msg_path.msg in
    let loc,mb = get_msg_body mbmap root iip msgn in
    begin match mb.port with
    | Some port ->
       Format.fprintf ppf
         "@[if (%s %s %s %s) {@]@;<0 2>@[<v>"
         _envport _self _adv port
    | None -> ()
    end
    ;
    Format.fprintf ppf "@[%s <- Some@]@;<0 2>@[<v>(%s.`enc@;"
      _r (qual_epdp_name loc msgn iip);
    Format.fprintf ppf "{|@;<0 2>@[<v>";
    let pfx = inter_id_path_str loc iip in
    Format.fprintf ppf "@[%s%s = %s;@]@;"
      pfx (name_record_func msgn) _self;
    begin match mb.port with
    | Some _ ->
      Format.fprintf ppf "@[%s%s = %a;@]@;"
        pfx (name_record_dir_port msgn mb) (pp_expr sc) (EcUtils.oget sat.msg_expr.port_expr)
    | None ->
      Format.fprintf ppf "@[%s%s = %s;@]@;"
        pfx (name_record_adv msgn) _adv
    end
    ;
    let pm = fst (List.split (params_map_to_list mb.params_map)) in
    let args = EcLocation.unloc sat.msg_expr.args in 
    List.iteri (fun i pn ->
        Format.fprintf ppf "@[%s%s = %a;@]@;"
        pfx (name_record msgn pn) (pp_expr sc) (List.nth args i)
      ) pm;
    Format.fprintf ppf "@]@;|}";
    Format.fprintf ppf ");@]@;";
    (*transition part*)
    Format.fprintf ppf "@[%s <- %s" _st (state_name (EcLocation.unloc sat.state_expr.id));
    List.iter (fun ex -> Format.fprintf ppf "@ %a"
      (pp_expr sc) ex) (EcLocation.unloc sat.state_expr.args);
    Format.fprintf ppf ";@]";
    begin match mb.port with
    | Some port ->
       Format.fprintf ppf "@]@;}"
    | None -> ()
    end   
  in
  let print_instruction ppf (it : instruction_tyd) : unit =
    match EcLocation.unloc it with
    | Assign (lhs, expr) -> ()
    | Sample (lhs, expr) -> ()
    | ITE (expr, thencode, elsecodeo) -> print_ite_instr expr thencode elsecodeo
    | Match (expr, mcl) -> ()
    | SendAndTransition sat -> print_sat_instr sat
    | Fail -> print_fail_instr ()
  in
  let code = EcLocation.unloc code in
  List.iter (fun it -> Format.fprintf ppf "%a@;" print_instruction it) code
  

let print_mmc_proc (sc : EcScope.scope) (root : string)
      (mbmap : message_body_tyd SLMap.t) (ppf : Format.formatter)
      (state_id : string) (params : ty_index Mid.t)
      (vars : (EcIdent.t * ty) EcLocation.located IdMap.t)
      (mmc : msg_match_clause_tyd) (state_name : string -> string): unit =
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
  print_code sc root mbmap ppf mmc.code  state_name;
  Format.fprintf ppf "@[return %s;@]" _r;
  Format.fprintf ppf "@]@;}@;"

let print_mmc_proc_call (ppf : Format.formatter)
      (state_id : string) (params : ty_index Mid.t) (mmc : msg_match_clause_tyd)
      (loc : bool) (msgn : string) (mb : message_body_tyd)
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
    let iip = (EcLocation.unloc mmc.msg_pat.msg_path_pat).inter_id_path in
    let pfx = _x^".`"^(inter_id_path_str loc iip) in
    List.map (fun r -> pfx^r) records
  in
  let params_list = fst (List.split (sparams_map_to_list params)) in
  let params_list = params_list @ (mmc_msg_pat_bindings mmc) in
  Format.fprintf ppf "@[%s %s %s (%a);@]"
    _r "<@" (mmc_proc_name state_id mmc.msg_pat.msg_path_pat state_name)
    print_proc_params_call params_list

let print_mmc_procs (sc : EcScope.scope) (root : string)
      (mbmap : message_body_tyd SLMap.t) (ppf : Format.formatter)
      (states : state_tyd IdMap.t) (state_name : string -> string) : unit =
  IdMap.iter(fun id st -> let st:state_body_tyd = EcLocation.unloc st in
    List.iter(fun mmc ->
      if UcSpecTypedSpecCommon.msg_path_pat_ends_star mmc.msg_pat.msg_path_pat
      then ()
      else print_mmc_proc sc root mbmap ppf id st.params st.vars mmc state_name
      ;) st.mmclauses
    ) states



let print_state_match_branch (root : string) (id : string)
      (mbmap : message_body_tyd SLMap.t)
      (ppf : Format.formatter) (st : state_tyd)
      (state_name : string -> string): unit =
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
      let msg_name = get_msg_name mmc.msg_pat.msg_path_pat in
      let iip = (EcLocation.unloc mmc.msg_pat.msg_path_pat).inter_id_path in
      let loc,mb = get_msg_body mbmap root iip msg_name in
      Format.fprintf ppf "@[match %s.`dec %s with@]@;"
        (qual_epdp_name loc msg_name (EcLocation.unloc mmc.msg_pat.msg_path_pat).inter_id_path) _m;
      Format.fprintf ppf "@[| Some %s => {@]@;<0 2>@[<v>" _x;
      print_mmc_proc_call ppf id st.params mmc loc msg_name mb state_name;
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

let print_state_match_branch_IF (root : string) (id : string)
      (mbmap : message_body_tyd SLMap.t)
      (ppf : Format.formatter) (st : state_tyd) : unit =
  print_state_match_branch root id mbmap ppf st state_name_IF

let print_proc_parties (sc : EcScope.scope)(root : string) (id : string)
      (mbmap : message_body_tyd SLMap.t) (ppf : Format.formatter)
      (ifbt : ideal_fun_body_tyd) : unit =
  Format.fprintf ppf "@[proc parties(%s : %a) : %a option = {@]@;<0 2>@[<v>"
    _m (pp_type sc) msg_ty (pp_type sc) msg_ty;
    Format.fprintf ppf "@[var %s : %a option <- None;@]@;"
      _r (pp_type sc) msg_ty;
    Format.fprintf ppf "@[match %s with@]@;" _st;
    IdMap.iter (fun id st -> Format.fprintf ppf "%a"
      (print_state_match_branch_IF root id mbmap) st) ifbt.states;
    Format.fprintf ppf "@[end;@]@;";
    Format.fprintf ppf "@[return %s;@]" _r;
    Format.fprintf ppf "@]@;}@;"
  

let print_ideal_module (sc : EcScope.scope) (root : string) (id : string)
      (mbmap : message_body_tyd SLMap.t) (ppf : Format.formatter)
      (ifbt : ideal_fun_body_tyd) : unit =
  let print_vars () =
     Format.fprintf ppf "@[var %s, %s : %a@]@;" _self _adv (pp_type sc) addr_ty;
     Format.fprintf ppf "@[var %s : %s@]@;" _st state_type_name_IF;
  in
  let print_proc_init () =
    Format.fprintf ppf "@[proc init(self_ adv_ : %a) : unit = {@]@;<0 2>"
    (pp_type sc) addr_ty;
    Format.fprintf ppf "@[%s <- self_; %s <- adv_; %s <- %s;@]@;@[}@]@;"
    _self _adv _st (state_name_IF (initial_state_id_of_states ifbt.states));
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
      "@[if ((%s.`1 = %s@ /\\@ %s.`2.`1 = %s@ /\\@ (%a)@ /\\@ envport %s %s %s.`3)@]"
         m mode_Dir m _self print_dir_pi_guard()  _self _adv m;
     Format.fprintf ppf "\\/";
     Format.fprintf ppf
       "@[@ (%s.`1 = %s@ /\\@ %s.`2.`1 = %s@ /\\@ %s.`2.`2 = %s.pi@ /\\@ %s.`3.`1 = %s))@]{"
          m mode_Adv m _self m (uc_name ifbt.id_adv_inter) m _adv;
    Format.fprintf ppf "@;<0 2>@[%s %s parties(%s);@]" r "<@" m;
    Format.fprintf ppf "@;}@]@;@[return %s;@]@;}@;" r
  in

  Format.fprintf ppf "@[module %s = {@]@;<0 2>@[<v>" (uc_name id);
  print_vars ();
  print_proc_init ();
  print_mmc_procs sc root mbmap ppf ifbt.states state_name_IF;
  print_proc_parties sc root id mbmap ppf ifbt;
  print_proc_invoke ();
  Format.fprintf ppf "@]@\n}.";
  ()
  

let gen_ideal_fun (sc : EcScope.scope) (root : string) (id : string)
      (mbmap : message_body_tyd SLMap.t) (ifbt : ideal_fun_body_tyd)
    : string = 
  let sf = Format.get_str_formatter () in
  Format.fprintf sf "@[<v>";
  Format.fprintf sf "@[%s@]@;@;" (open_theory uc__if);
  Format.fprintf sf "@[%a@]@;@;" (print_state_type_IF sc) ifbt.states;
  Format.fprintf sf "@[%a@]@;@;" (print_ideal_module sc root id mbmap) ifbt;
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
      (rfbt : real_fun_body_tyd) : unit =
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
  let np = IdMap.cardinal rfbt.params in
  let ps = indexed_map_to_list_keep_keys rfbt.params in 
  for n = 0 to np-1 do
    let pn = fst (List.nth ps n) in
    print_addr_op pn (n+1)
  done;
  Format.fprintf ppf "@;";
  let nsf = IdMap.cardinal rfbt.sub_funs in
  let sfbndgs = IdMap.bindings rfbt.sub_funs in
  for n = 0 to nsf-1 do
    let isf_name = fst (List.nth sfbndgs n) in
    print_addr_op isf_name (np+n+1)
  done;
  Format.fprintf ppf "@;";
  let npt = IdMap.cardinal rfbt.parties in
  let ptbndgs = IdMap.bindings rfbt.parties in
  for n = 0 to npt-1 do
    let ptn = fst (List.nth ptbndgs n) in
    print_extport_op ptn (n+1)
  done;
  Format.fprintf ppf "@;";
  for n = 0 to npt-1 do
    let ptn = fst (List.nth ptbndgs n) in
    print_intport_op ptn (npt+n+1)
  done;
  Format.fprintf ppf "@]@;"

let print_party_types (sc : EcScope.scope) (ppf : Format.formatter)
      (parties : party_tyd IdMap.t) : unit =
  Format.fprintf ppf "@[<v>";
  IdMap.iter (fun (pn : string) (pt : party_tyd) ->
      print_state_type sc ppf (EcLocation.unloc pt).states
        (state_type_name_pt pn) (state_name_pt pn);
    ) parties;
  Format.fprintf ppf "@]"

let print_real_module (sc : EcScope.scope) (root : string) (id : string)
      (mbmap : message_body_tyd SLMap.t) (ppf : Format.formatter)
      (rfbt : real_fun_body_tyd) : unit =
  let print_vars () =
     Format.fprintf ppf "@[var %s, %s : %a@]@;" _self _adv (pp_type sc) addr_ty;
     IdMap.iter (fun pn _ ->
         Format.fprintf ppf "@[var %s : %s@]@;"
           (st_name pn) (state_type_name_pt pn)  
       ) rfbt.parties;
     Format.fprintf ppf "@;"
  in
  let print_proc_init () =
    Format.fprintf ppf "@[proc init(self_ adv_ : %a) : unit = {@]@;<0 2>"
    (pp_type sc) addr_ty;
    Format.fprintf ppf "@[%s <- self_; %s <- adv_;@]@;"
      _self _adv;
    IdMap.iter (fun sfn (sfr, sfid) ->
      Format.fprintf ppf "@[%s.%s.%s.%s.init(%s %s, %s);@]@;"
      (uc_name sfn) uc__code uc__if (uc_name sfid) (addr_op_name sfn) _self _adv  ) rfbt.sub_funs;
    IdMap.iter (fun pn pt ->
    Format.fprintf ppf "@[ %s <- %s;@]@;"
      (st_name pn) (state_name_pt pn (initial_state_id_of_party_tyd  pt))
      ) rfbt.parties;
    Format.fprintf ppf "@[}@]@;"
  in
  let print_proc_invoke () =
 (*   let r, m = "r", "m" in
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
      "@[if ((%s.`1 = %s@ /\\@ %s.`2.`1 = %s@ /\\@ (%a)@ /\\@ envport %s %s %s.`3)@]"
         m mode_Dir m _self print_dir_pi_guard()  _self _adv m;
     Format.fprintf ppf "\\/";
     Format.fprintf ppf
       "@[@ (%s.`1 = %s@ /\\@ %s.`2.`1 = %s@ /\\@ %s.`2.`2 = %s.pi@ /\\@ %s.`3.`1 = %s))@]{"
          m mode_Adv m _self m (uc_name ifbt.id_adv_inter) m _adv;
    Format.fprintf ppf "@;<0 2>@[%s %s parties(%s);@]" r "<@" m;
    Format.fprintf ppf "@;}@]@;@[return %s;@]@;}@;" r
    *)()
  in

  Format.fprintf ppf "@[module %s = {@]@;<0 2>@[<v>" (uc_name id);
  print_vars ();
  print_proc_init ();
(*  print_mmc_procs sc root mbmap ppf ifbt.states state_name_IF;
  print_proc_parties sc root id mbmap ppf ifbt;*)
  print_proc_invoke ();
  Format.fprintf ppf "@]@\n}.";
  
  ()


let gen_real_fun (sc : EcScope.scope) (root : string) (id : string)
      (mbmap : message_body_tyd SLMap.t) (rfbt : real_fun_body_tyd)
    : string = 
  let sf = Format.get_str_formatter () in
  Format.fprintf sf "@[<v>";
  Format.fprintf sf "@[%s@]@;@;" (open_theory uc__rf);
  Format.fprintf sf "@[%a@]@;@;" print_sub_fun_clones rfbt;
  Format.fprintf sf "@[%a@]@;@;" (print_addr_and_port_operators sc) rfbt;
  Format.fprintf sf "@[%a@]@;@;" (print_party_types sc) rfbt.parties;
  Format.fprintf sf "@[%a@]@;@;" (print_real_module sc root id mbmap) rfbt;
  Format.fprintf sf "@[%s@]@;" (close_theory uc__rf);
  Format.fprintf sf "@]";
  Format.flush_str_formatter ()

let gen_fun (sc : EcScope.scope) (root : string) (id : string)
      (mbmap : message_body_tyd SLMap.t) (ft : fun_tyd)
    : string =
  let fbt = EcLocation.unloc ft in
  match fbt with
  | FunBodyIdealTyd ifbt -> gen_ideal_fun sc root id mbmap ifbt
  | FunBodyRealTyd rfbt  -> gen_real_fun sc root id mbmap rfbt

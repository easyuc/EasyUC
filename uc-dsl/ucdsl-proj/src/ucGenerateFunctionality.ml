open UcTypedSpec
open UcSpecTypedSpecCommon
open EcTypes
open UcGenerateCommon

let state_name (name : string) : string = "_State_"^name
let state_type_name = "_state"
let uc__if = "UC__IF"
let _self = "_self"
let _adv = "_adv"
let _st = "_st"
let _m = "_m"
let _r = "_r"
let _x = "_x"
let msg_ty : ty =
  tconstr (EcPath.fromqsymbol (uc_qsym_prefix_basic_types, "msg")) []


let print_state_type
      (sc : EcScope.scope)
      (ppf : Format.formatter)
      (states : state_tyd IdMap.t)
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

let mmc_proc_name (stid : string) (mpp : msg_path_pat)
    : string =
  let mpp = EcLocation.unloc mpp in
  let stn = state_name stid in
  let msgn = match mpp.msg_or_star with
    | MsgOrStarMsg s -> s
    | MsgOrStarStar -> UcMessage.failure "not possible" in
  (List.fold_left (fun n p -> n^"__"^p) stn mpp.inter_id_path)^"__"^msgn

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

let mmc_epdp_name (loc : bool) (msgn : string) (mpp : msg_path_pat)
    : string =
  let mpp = EcLocation.unloc mpp in
  let _mty_name = msg_ty_name msgn in
  let _epdp_op_name = epdp_op_name _mty_name in
  (inter_id_path_str loc mpp.inter_id_path)^_epdp_op_name
  
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

let rec print_code (sc :  EcScope.scope) (ppf : Format.formatter)
          (code : instruction_tyd list EcLocation.located) : unit =
  let print_fail_instr () : unit =
    Format.fprintf ppf "@[%s <- None;@]" _r
  in
  let print_ite_instr expr thencode elsecodeo : unit =
    Format.fprintf ppf "@[if (%a) {@]@;<0 2>@[<v>" (pp_expr sc) expr;
    print_code sc ppf thencode;
    Format.fprintf ppf  "@]@;}";
    match elsecodeo with
    | Some code ->
      Format.fprintf ppf "@;@[else {@]@;<0 2>@[<v>";
      print_code sc ppf code; 
      Format.fprintf ppf  "@]@;}"
    | None -> ()
  in
  let print_instruction ppf (it : instruction_tyd) : unit =
    match EcLocation.unloc it with
    | Assign (lhs, expr) -> ()
    | Sample (lhs, expr) -> ()
    | ITE (expr, thencode, elsecodeo) -> print_ite_instr expr thencode elsecodeo
    | Match (expr, mcl) -> ()
    | SendAndTransition sat -> print_fail_instr ()
    | Fail -> print_fail_instr ()
  in
  let code = EcLocation.unloc code in
  List.iter (fun it -> Format.fprintf ppf "%a@;" print_instruction it) code
  

let print_mmc_proc (sc : EcScope.scope) (ppf : Format.formatter)
      (state_id : string) (params : ty_index Mid.t)
      (vars : (EcIdent.t * ty) EcLocation.located IdMap.t)
      (mmc : msg_match_clause_tyd) : unit =
  Format.fprintf ppf "@[proc %s (%a) : %a option = {@]@;<0 2>@[<v>"
    (mmc_proc_name state_id mmc.msg_pat.msg_path_pat)
    (print_proc_params_decl sc) ((sparams_map_to_list params)@(
      List.map (fun (id,t) -> ((EcIdent.name id),t)) (msg_match_clause_msg_pat_bindings mmc)))
    (pp_type sc) msg_ty;
  IdMap.iter (fun id l -> let (ident,ty) = EcLocation.unloc l in
      Format.fprintf ppf "@[var %s : %a;@]@;"
              (EcIdent.name ident) (pp_type sc) ty
    ) vars;
  Format.fprintf ppf "@[var %s : %a option;@]@;" _r (pp_type sc) msg_ty;
  print_code sc ppf mmc.code;
  Format.fprintf ppf "@[return %s;@]" _r;
  Format.fprintf ppf "@]@;}@;"

let print_mmc_proc_call (ppf : Format.formatter)
      (state_id : string) (params : ty_index Mid.t) (mmc : msg_match_clause_tyd)
      (loc : bool) (msgn : string) (mb : message_body_tyd) : unit =
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
    _r "<@" (mmc_proc_name state_id mmc.msg_pat.msg_path_pat)
    print_proc_params_call params_list

let print_mmc_procs (sc : EcScope.scope) (ppf : Format.formatter)
      (states : state_tyd IdMap.t) : unit =
  IdMap.iter(fun id st -> let st:state_body_tyd = EcLocation.unloc st in
    List.iter(fun mmc ->
      if UcSpecTypedSpecCommon.msg_path_pat_ends_star mmc.msg_pat.msg_path_pat
      then ()
      else print_mmc_proc sc ppf id st.params st.vars mmc
      ;) st.mmclauses
    ) states



let print_state_match_branch (root : string) (id : string)
      (mbmap : message_body_tyd SLMap.t)
      (ppf : Format.formatter) (st : state_tyd) : unit =
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
      let loc,msg_name,mb = get_msg_body mbmap root mmc.msg_pat.msg_path_pat in
      Format.fprintf ppf "@[match %s.`dec %s with@]@;"
        (mmc_epdp_name loc msg_name mmc.msg_pat.msg_path_pat) _m;
      Format.fprintf ppf "@[| Some %s => {@]@;<0 2>@[<v>" _x;
      print_mmc_proc_call ppf id st.params mmc loc msg_name mb;
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
      (mbmap : message_body_tyd SLMap.t) (ppf : Format.formatter)
      (ifbt : ideal_fun_body_tyd) : unit =
  Format.fprintf ppf "@[proc parties(%s : %a) : %a option = {@]@;<0 2>@[<v>"
    _m (pp_type sc) msg_ty (pp_type sc) msg_ty;
    Format.fprintf ppf "@[var %s : %a option <- None;@]@;"
      _r (pp_type sc) msg_ty;
    Format.fprintf ppf "@[match %s with@]@;" _st;
    IdMap.iter (fun id st -> Format.fprintf ppf "%a"
      (print_state_match_branch root id mbmap) st) ifbt.states;
    Format.fprintf ppf "@[end;@]@;";
    Format.fprintf ppf "@[return %s;@]" _r;
    Format.fprintf ppf "@]@;}"
  

let print_ideal_module (sc : EcScope.scope) (root : string) (id : string)
      (mbmap : message_body_tyd SLMap.t) (ppf : Format.formatter)
      (ifbt : ideal_fun_body_tyd) : unit =
  let print_vars () =
     Format.fprintf ppf "@[var %s, %s : %a@]@;" _self _adv (pp_type sc) addr_ty;
     Format.fprintf ppf "@[var %s : %s@]@;" _st state_type_name;
  in
  let print_proc_init () =
    Format.fprintf ppf "@[proc init(self_ adv_ : %a) : unit = {@]@;<0 2>"
    (pp_type sc) addr_ty;
    Format.fprintf ppf "@[%s <- self_; %s <- adv_; %s <- %s;@]@;@[}@]@;"
    _self _adv _st (state_name (initial_state_id_of_states ifbt.states));
  in
  Format.fprintf ppf "@[module %s = {@]@;<0 2>@[<v>" (uc_name id);
  print_vars ();
  print_proc_init ();
  print_mmc_procs sc ppf ifbt.states;
  print_proc_parties sc root id mbmap ppf ifbt;
  Format.fprintf ppf "@]@;}.";
  ()
  

let gen_ideal_fun (sc : EcScope.scope) (root : string) (id : string)
      (mbmap : message_body_tyd SLMap.t) (ifbt : ideal_fun_body_tyd)
    : string = 
  let sf = Format.get_str_formatter () in
  Format.fprintf sf "@[<v>@,@,";
  Format.fprintf sf "@[%s@]@,@," (open_theory uc__if);
  Format.fprintf sf "@[%a@]@," (print_state_type sc) ifbt.states;
  Format.fprintf sf "@[%a@]@," (print_ideal_module sc root id mbmap) ifbt;
  Format.fprintf sf "@[%s@]@," (close_theory uc__if);
  Format.fprintf sf "@]";
  Format.flush_str_formatter ()

let gen_fun (sc : EcScope.scope) (root : string) (id : string)
      (mbmap : message_body_tyd SLMap.t) (ft : fun_tyd)
    : string =
  let fbt = EcLocation.unloc ft in
  match fbt with
  | FunBodyIdealTyd ifbt -> gen_ideal_fun sc root id mbmap ifbt
  | FunBodyRealTyd rfbt  -> ""

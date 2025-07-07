open UcTypedSpec
open UcSpecTypedSpecCommon
open EcTypes
open UcGenerateCommon

let state_name_IF (name : string) : string = "_State_IF_"^name
let state_type_name_IF = "_state_IF"

let state_name_SIM (name : string) : string = "_State_SIM_"^name
let state_type_name_SIM = "_state_SIM"

let state_name_pt (ptname : string) (sname : string) : string =
  "_State_"^ptname^"_"^sname
let state_type_name_pt (ptname : string) : string =
  "_state_"^ptname

let _m = "_m"
let _r = "_r"
let _x = "_x"
let _envport = "envport"
let msg_ty : ty =
  tconstr (EcPath.fromqsymbol (uc_qsym_prefix_basic_types, "msg")) []
let parties_str = "parties"
let loop_str = "loop"
let proc_party_str (pn : string) = "party_"^pn
let addr_op_call_sim (name : string) : string =
  (addr_op_name name)^" "^oget_if_addr_opt

let _metric_pt_good ptn = "_metric_"^ptn^"_good"

let module_params_string pmns : string =
  if pmns = []
  then ""
  else
    let hd = List.hd pmns in
    let tl = List.tl pmns in
    (List.fold_left (fun acc pmn -> acc^", "^pmn) ("("^hd) tl)^")"

let _RFIP = "RFIP"
let smt_sat_lemmas = "mem_oflist mem_rangeset in_fsetU"
let smt_invoke_lemmas = "mem_oflist mem_rangeset iota0 iota1 fset0U fsetU0 in_fsetU"

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
  let pp_ex = pp_form ~is_sim:(sim_uses<>None) ~intprts:intprts ~glob_pfx:glob_pfx sc in
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
  let print_ite_instr form thencode elsecodeo : unit =
    Format.fprintf ppf "@[if (%a) {@]@;<0 2>@[<v>" pp_ex form;
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
  let print_assign_instr lhs form =
    Format.fprintf ppf "@[%a <- %a;@]" print_lhs lhs pp_ex form
  in
  let print_sample_instr lhs form =
    Format.fprintf ppf "@[%a <$ %a;@]" print_lhs lhs pp_ex form
  in
  let print_match_instr form (mcl:match_clause_tyd list) =
    let ety = EcFol.f_ty form in
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
      (pp_form sc) form (EcPrinting.pp_list "" pp_branch) mcl
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
    | Assign (lhs, form) -> print_assign_instr lhs form
    | Sample (lhs, form) -> print_sample_instr lhs form
    | ITE (form, thencode, elsecodeo) -> print_ite_instr form thencode elsecodeo
    | Match (form, mcl) -> print_match_instr form (EcLocation.unloc mcl)
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
    _self _st (state_name_IF (initial_state_id_of_states ifbt.states));
  in
  let print_proc_invoke () =
    let r, m = "r", "m" in
    Format.fprintf ppf "@[proc %s(%s : %a) : %a option = {@]@;<0 2>@[<v>"
      invoke m (pp_type sc) msg_ty (pp_type sc) msg_ty;
    Format.fprintf ppf "@[var %s : %a option <- None;@]@;"
      r (pp_type sc) msg_ty;
    Format.fprintf ppf
      "@[if ((%s.`1 = %s@ /\\@ %s.`2.`1 = %s@ /\\@ envport %s %s.`3)@]"
      m mode_Dir m _self _self m;
    if ifbt.id_adv_inter<>None
    then begin 
     Format.fprintf ppf "\\/";
     Format.fprintf ppf
       "@[@ (%s.`1 = %s@ /\\@ %s.`2.`1 = %s@ /\\@ %s.`3.`1 = %s))@]{"
       m mode_Adv m _self m adv
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
    sc root mbmap ppf ifbt.states state_name_IF dii IdPairMap.empty None "";
  print_proc_parties
    sc root id mbmap parties_str state_name_IF dii ppf ifbt.states None;
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
      (mbmap : message_body_tyd SLMap.t) (dii : symb_pair IdMap.t) (ais : symb_pair IdPairMap.t)
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
              | Assign (lhs, form) ->
                 Format.fprintf ppf "@[sp 1. (*Assign instruction*)@]@;"
              | Sample (lhs, form) ->
                 Format.fprintf ppf
                 "@[seq 1 : (#pre). rnd. skip. move => />;smt(). (*Sample instruction*)@]@;"
              | ITE (form, thencode, elsecodeo) -> begin
                  Format.fprintf ppf "@[if. (*if instruction*)@]@;";
                   print_proof_code ppf thencode;
                   if elsecodeo <> None then
                     print_proof_code ppf (EcUtils.oget elsecodeo)
                   end
              | Match (form, mcl) -> begin
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
                   get_msg_info mp dii ais root mbmap in
                 let envportcheck = (not is_internal) && (mb.port <> None) in
                 if envportcheck
                 then Format.fprintf ppf "@[if. (*envport check*)@]@;"
                 ;  
                 Format.fprintf ppf
                   "@[%s sp 3. skip. move => />;smt(%s). (*SendAndTransition instruction*)@]@;"
                   ret_pfx smt_sat_lemmas;
                 if envportcheck
                 then
                   Format.fprintf ppf
                   "@[%s sp 1. skip. move => />;smt(). (*envport check failed case*)@]@;"
                   ret_pfx
                end
              | Fail ->
                 Format.fprintf ppf
                   "@[%s sp 2. skip. move => />;smt(). (*Fail instruction*)@]@;" ret_pfx
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
            get_msg_info mp dii ais root mbmap in
          Format.fprintf ppf "@[match. (*message match*)@]@;";
          Format.fprintf ppf
            "@[%s skip. move => />;smt(). (*None branch of message match, dec failed*)@]@;"
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
              "@[%s skip. move => />;smt(). (*address check for internal messages failed case*)@]@;"
              ret_pfx
          ;
      in
      
  let mmcs = List.filter (fun mmc -> not
    (UcSpecTypedSpecCommon.msg_path_pat_ends_star mmc.msg_pat.msg_path_pat)
               ) st.mmclauses in
  if List.is_empty mmcs
  then 
    Format.fprintf ppf
            "@[%s skip. move => />;smt(). (*empty state match branch code*)@]@;" ret_pfx
  else
    print_proof_mm ppf mmcs;
  in
  Format.fprintf ppf "@[%s sp 1. (*initializing input, return value*)@]@;"
    ret_pfx;
  Format.fprintf ppf "@[match. (*state match*)@]@;";
  IdMap.iter (fun id st -> Format.fprintf ppf "(*state branch %s*) %a" id
                             print_proof_state_match_branch st) st_map

let print_lemma_metric_invoke
      (metric_name : string)
      (invar_name : string)
      (module_name : string) 
      (root : string)
      (mbmap : message_body_tyd SLMap.t) (dii : symb_pair IdMap.t) (ais : symb_pair IdPairMap.t)
      (ppf : Format.formatter) (st_map : state_tyd IdMap.t) : unit =    
  Format.fprintf ppf "@[lemma %s (n : int) : hoare [@]@;<0 2>@[<v>" iF_invoke;
  Format.fprintf ppf
    "%s.%s :@ %s (glob %s) /\\ %s (glob %s) = n@ ==>@ "
    module_name invoke invar_name  module_name metric_name module_name;
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
  print_proof_state_match root mbmap dii ais "sp 1." ppf st_map;
  Format.fprintf ppf "@[skip. smt(). (*invoke guard false*)@]@;";
  Format.fprintf ppf "@[qed.@]@;"

let print_IF_lemma_metric_invoke (module_name : string) 
      (root : string)
      (mbmap : message_body_tyd SLMap.t) (dii : symb_pair IdMap.t)
      (ppf : Format.formatter) (st_map : state_tyd IdMap.t) : unit =
  Format.fprintf ppf "@[%a@]" (print_lemma_metric_invoke
                               uc_metric_name_IF
                                 _invar_IF
                                 module_name
                                 root
                                 mbmap
                                 dii
                                 IdPairMap.empty
    ) st_map


let print_SIM_proof_state_match (root : string)
      (mbmap : message_body_tyd SLMap.t) (ais : symb_pair IdPairMap.t)
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
              | Assign (lhs, form) ->
                 Format.fprintf ppf "@[sp 1. (*Assign instruction*)@]@;"
              | Sample (lhs, form) ->
                 Format.fprintf ppf
                 "@[seq 1 : (#pre). rnd. skip. move => />;smt(). (*Sample instruction*)@]@;"
              | ITE (form, thencode, elsecodeo) -> begin
                  Format.fprintf ppf "@[if. (*if instruction*)@]@;";
                   print_proof_code ppf thencode;
                   if elsecodeo <> None then
                     print_proof_code ppf (EcUtils.oget elsecodeo)
                   end
              | Match (form, mcl) -> begin
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
                 let _, _, _, _, mb, _ =
                   get_msg_info mp IdMap.empty ais root mbmap in
                 let envportcheck = (mb.port <> None) in
                 if envportcheck
                 then Format.fprintf ppf "@[if. (*envport check*)@]@;"
                 ;  
                 Format.fprintf ppf
                   "@[%s sp 2. skip. move => />;smt(). (*SendAndTransition instruction*)@]@;"
                   ret_pfx;
                 if envportcheck
                 then
                   Format.fprintf ppf
                   "@[%s sp 1. skip. move => />;smt(). (*envport check failed case*)@]@;"
                   ret_pfx
                end
              | Fail ->
                 Format.fprintf ppf
                   "@[%s sp 2. skip. move => />;smt(). (*Fail instruction*)@]@;" ret_pfx
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
          Format.fprintf ppf "@[if;last first. (*message guard*)@]@;";
          Format.fprintf ppf
            "@[%s skip. move => />;smt(). (*message guard failed*)@]@;"
            ret_pfx;
          
            Format.fprintf ppf
            "@[sp %i. (*state param assignment, return value initialization*)@]"
              ((Mid.cardinal st.params) + 1);
          print_proof_mmc ppf mmc;
          print_proof_mm ppf (List.tl mmcs);
          
      in
      
  let mmcs = List.filter (fun mmc -> not
    (UcSpecTypedSpecCommon.msg_path_pat_ends_star mmc.msg_pat.msg_path_pat)
               ) st.mmclauses in
  if List.is_empty mmcs
  then 
    Format.fprintf ppf
            "@[%s skip. move => />;smt(). (*empty state match branch code*)@]@;" ret_pfx
  else
    print_proof_mm ppf mmcs;
  in
  Format.fprintf ppf "@[match. (*state match*)@]@;";
  IdMap.iter (fun id st -> Format.fprintf ppf "(*state branch %s*) %a" id
                             print_proof_state_match_branch st) st_map

let print_SIM_lemma_metric_invoke
      (module_name : string) 
      (root : string)
      (mbmap : message_body_tyd SLMap.t) (ais : symb_pair IdPairMap.t)
      (ppf : Format.formatter) (st_map : state_tyd IdMap.t) : unit =
  let metric_name = (uc_metric_name_SIM module_name) in
  let invar_name = (_invar_SIM module_name) in
  Format.fprintf ppf "@[lemma %s (n : int) : hoare [@]@;<0 2>@[<v>" (sIM_invoke module_name);
  Format.fprintf ppf
    "%s.%s :@ %s (glob %s) /\\ %s (glob %s) = n@ ==>@ "
    module_name invoke invar_name  module_name metric_name module_name;
  Format.fprintf ppf
    "res <> None =>@ %s (glob %s) < n@;"
    metric_name module_name;
  Format.fprintf ppf "@]@;].@;";
  Format.fprintf ppf "@[proof.@]@;";
  Format.fprintf ppf "@[rewrite /%s /=.@]@;" metric_name;
  Format.fprintf ppf "@[proc.@]@;";
  Format.fprintf ppf "@[sp 1. (*initializing return value*)@]@;";
  Format.fprintf ppf "@[seq 1 : (#pre /\\ %s.if_addr_opt <> None). sp 1. auto;smt(). (*if_addr_opt initialized after first message is received*)@]@;" module_name;
  Format.fprintf ppf "@[inline.@]@;";
  print_SIM_proof_state_match root mbmap ais "sp 1." ppf st_map;
  Format.fprintf ppf "@[qed.@]@;"
  
let print_ctor_args_state_metric (st_id : string)  (ppf : Format.formatter)
      (st_map : state_tyd IdMap.t) : unit =
    let s = IdMap.find st_id st_map in
    let sb = EcLocation.unloc s in
    Mid.iter (fun _ _ -> Format.fprintf ppf "_ " ) sb.params

let print_state_metric
(state_pos_in_glob : int)
(state_name : string -> string)
(state_type_name : string)
  (metric_name : string)
  (module_name : string)
  (ppf : Format.formatter) (st_map : state_tyd IdMap.t) : unit =
  let lin = linearize_state_DAG st_map in
  match lin with
  | None -> Format.fprintf ppf
              "@[(*cannot generate operator %s, states have cycles*)@]"
              metric_name
  | Some id_lvl_map ->
     begin
     let globopname = glob_to_part_op_name module_name _st in
     Format.fprintf ppf "@[op %s (g : glob %s) / : %s = g.`%i.@]@;"
     globopname module_name state_type_name state_pos_in_glob;
     Format.fprintf ppf
       "@[<v>@[op [smt_opaque] %s (g : glob %s) : int =@]@;<0 2>@[<v>"
       metric_name  module_name;
     Format.fprintf ppf "@[match %s g with@]@;" globopname;
     IdMap.iter (fun id lvl ->
         Format.fprintf ppf "@[| %s %a=> %i@]@;"
           (state_name id) (print_ctor_args_state_metric id) st_map lvl
       ) id_lvl_map;
     Format.fprintf ppf "@[end.@]@;@]@;@]"
     end

let print_IF_state_metric (module_name : string)
      (ppf : Format.formatter) (st_map : state_tyd IdMap.t) : unit =
  Format.fprintf ppf "@[%a@]" (print_state_metric
                               2
                               state_name_IF
                               state_type_name_IF
                               uc_metric_name_IF
                               module_name
    ) st_map

let print_SIM_state_metric (module_name : string)
      (ppf : Format.formatter) (st_map : state_tyd IdMap.t) : unit =
  Format.fprintf ppf "@[%a@]" (print_state_metric
                               1
                               state_name_SIM
                               state_type_name_SIM
                               (uc_metric_name_SIM module_name)
                               module_name
    ) st_map


let print_IF_metric (id : string)(root : string)
      (mbmap : message_body_tyd SLMap.t) (dii : symb_pair IdMap.t)
      (ppf : Format.formatter) (st_map : state_tyd IdMap.t)
    : unit =
    Format.fprintf ppf "@[%a@]@;@;"
    (print_IF_state_metric (uc_name id))
    st_map;
  Format.fprintf ppf "@[%a@]@;@;"
    (print_IF_lemma_metric_invoke (uc_name id) root mbmap dii)
    st_map

let print_SIM_metric (id : string)(root : string)
      (mbmap : message_body_tyd SLMap.t) (ais : symb_pair IdPairMap.t)
      (ppf : Format.formatter) (st_map : state_tyd IdMap.t)
    : unit =
    Format.fprintf ppf "@[%a@]@;@;"
    (print_SIM_state_metric (uc_name id))
    st_map;
  Format.fprintf ppf "@[%a@]@;@;"
    (print_SIM_lemma_metric_invoke (uc_name id) root mbmap ais)
    st_map

let print_IF_invar
      (ppf : Format.formatter) (id : string) : unit =
  Format.fprintf ppf "@[<v>@;";
  Format.fprintf ppf "@[(*alias*)@]@;";
  Format.fprintf ppf "@[module IF = %s.@]@;" (uc_name id);
  Format.fprintf ppf "@[op %s (g : glob IF) : bool = predT g.@]@;@;" _invar_IF;
  Format.fprintf ppf "@]@;"

let print_SIM_invar
      (ppf : Format.formatter) (id : string) : unit =
  let module_name = uc_name id in
  Format.fprintf ppf "@[<v>@;";
  Format.fprintf ppf "@[op %s (g : glob %s) : bool = predT g.@]@;@;" (_invar_SIM module_name) module_name;
  Format.fprintf ppf "@]@;"


let print_IF_metric_good_init_lemmas
      (ppf : Format.formatter) (_ : unit): unit =
  Format.fprintf ppf "@[lemma %s (g : glob IF) :@]@;"  iF_metric_good;
  Format.fprintf ppf "@[  %s g => 0 <= %s g.@]@;" _invar_IF uc_metric_name_IF;
  Format.fprintf ppf "@[  proof. rewrite /%s /=.@]@;" uc_metric_name_IF;
  Format.fprintf ppf "@[  smt(). qed.@]@;@;@;";
  Format.fprintf ppf "@[lemma IF_init :@]@;";
  Format.fprintf ppf "@[  hoare [IF.init : true ==> %s (glob IF)].@]@;"
    _invar_IF;
  Format.fprintf ppf "@[proof. proc. auto. qed.@]@;";
  Format.fprintf ppf "@]@;"

let print_SIM_metric_good_init_lemmas
      (ppf : Format.formatter) (module_name : string): unit =
  Format.fprintf ppf "@[lemma %s (g : glob %s) :@]@;"  (sIM_metric_good module_name) module_name;
  Format.fprintf ppf "@[  %s g => 0 <= %s g.@]@;" (_invar_SIM module_name) (uc_metric_name_SIM module_name);
  Format.fprintf ppf "@[  proof. rewrite /%s /=.@]@;" (uc_metric_name_SIM module_name);
  Format.fprintf ppf "@[  smt(). qed.@]@;@;@;";
  Format.fprintf ppf "@[lemma %s_init :@]@;" module_name;
  Format.fprintf ppf "@[  hoare [%s.init : true ==> %s (glob %s)].@]@;"
    module_name (_invar_SIM module_name) module_name;
  Format.fprintf ppf "@[proof. proc. auto. qed.@]@;";
  Format.fprintf ppf "@]@;"

let gen_ideal_fun (sc : EcScope.scope) (root : string) (id : string)
      (mbmap : message_body_tyd SLMap.t) (ifbt : ideal_fun_body_tyd)
      (dii : symb_pair IdMap.t) : string =
  let sf = Format.get_str_formatter () in
  Format.fprintf sf "@[<v>";
  if ifbt.id_adv_inter<>None
  then clone_adv_inter sf (EcUtils.oget ifbt.id_adv_inter);
  Format.fprintf sf "@[%a@]@;@;" (print_state_type_IF sc) ifbt.states;
  Format.fprintf sf "@[%a@]@;@;" (print_ideal_module sc root id mbmap dii) ifbt;
  Format.fprintf sf "@[%a@]@;@;" print_IF_invar id;
  Format.fprintf sf "%a" (print_IF_metric id root mbmap dii) ifbt.states;
  Format.fprintf sf "@[%a@]@;@;" print_IF_metric_good_init_lemmas ();
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

  let subfunpath sfn sfid = (uc_name sfn)^"."^(uc_name sfid)
  
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
  let rest_module_name = rest_name id drop_param in
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
      IdMap.iter (fun pmn _ -> Format.fprintf ppf " - %s.%s"
        (uc_name pmn)  adv_pi_num_op_name) rfbt.params
  in
  let begin_param_pis ppf rfbt =
      if IdMap.is_empty rfbt.params
      then ()
      else
        List.iteri (fun i (pmn, _) ->
            if i>0 then Format.fprintf ppf "; "
            ;
            Format.fprintf ppf "%s"
              (adv_pi_begin_param pmn)) (indexed_map_to_list_keep_keys
                                           rfbt.params)
  in
  let end_param_pis ppf rfbt =
      if IdMap.is_empty rfbt.params
      then ()
      else
        List.iteri (fun i (pmn, _) ->
            let nm = uc_name pmn in
            if i>0 then Format.fprintf ppf "; "
            ;
            Format.fprintf ppf "%s + %s.%s - 1"
            (adv_pi_begin_param pmn) nm adv_pi_num_op_name)
          (indexed_map_to_list_keep_keys rfbt.params)
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
(id,rfbt,gvil : string * real_fun_body_tyd * gvil) : unit =
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
    Format.fprintf ppf "@[op %s <- %s@]@;" rf_info rf_info;
  Format.fprintf ppf "@[proof *.@]@;";
  Format.fprintf ppf "@[realize rf_info_valid. smt(%s). qed.@]@;@;"
    adv_pi_begin_gt0_axiom_name
  in
  let print_MakeRF_and_lemmas
        (gvil : globVarId list)
        (core_module : string)
        (makeRF_module : string)
        (core_invar_op : string)
        (core_init_lemma : string)
        (core_metric_op : string)
        (core_invoke_lemma : string)
        (core_metric_good_lemma : string)
    =
    let makeRF_core_init_invar_lemma = makeRF_module^"_Core_init" in
    let makeRF_core_invoke_lemma = makeRF_module^"_Core_invoke" in
    let glob_op_name = "glob_"^makeRF_module^"_to_Core" in
    let makeRF_init_invar_lemma = makeRF_init_invar_lemma makeRF_module in
    let makeRF_invoke_lemma = makeRF_invoke_lemma makeRF_module in
    let makeRF_invar_op = makeRF_invar_op makeRF_module in
    let makeRF_metric_op = makeRF_metric_op makeRF_module in
    let makeRF_metric_good_lemma = makeRF_metric_good_lemma makeRF_module in
    Format.fprintf ppf
      "@[module %s = RFCore.MakeRF(%s).@]@;@;"
      makeRF_module
    core_module;
    Format.fprintf ppf
"@[lemma %s :
  hoare [%s.init : true ==> %s (glob %s)].
proof.
apply (RFCore.MakeRF_init_invar_hoare (%s) %s).
apply %s.
 qed.@]@;@;"
      makeRF_core_init_invar_lemma
      makeRF_module core_invar_op  core_module
      core_module core_invar_op
      core_init_lemma;
    Format.fprintf ppf
"@[lemma %s (n : int) :
  hoare
  [%s.invoke :
   %s (glob %s) /\\ %s (glob %s) = n ==>
   %s (glob %s) /\\@;
 (res <> None => %s (glob %s) < n@;
 /\\ ((oget res).`1 = Adv => (oget res).`2.`2 \\in  adv_pis_rf_info rf_info))].
proof.
apply (RFCore.MakeRF_invoke_term_metric_hoare (%s) %s %s).
apply %s.
 qed.@]@;@;"
makeRF_core_invoke_lemma
makeRF_module
core_invar_op core_module
core_metric_op core_module
core_invar_op core_module
core_metric_op core_module
core_module core_invar_op core_metric_op
    core_invoke_lemma;
    Format.fprintf ppf
      "@[(* now we lift our invariant, termination metric and lemmas to %s *)@]@;@;"
      makeRF_module;
    let range = get_MakeRFs_glob_range_of_real_fun_glob_core gvil in
    Format.fprintf ppf "@[%a@]@;@;"
    (print_glob_operator glob_op_name makeRF_module core_module) range;
    Format.fprintf ppf
"@[op %s : glob %s -> bool =
  fun (g : glob %s) => %s (%s g).

op %s : glob %s -> int =
  fun (g : glob %s) => %s (%s g).

lemma %s (g : glob %s) :
  %s g => 0 <= %s g.
    proof.
 smt(%s). qed.
 "
makeRF_invar_op makeRF_module
makeRF_module core_invar_op glob_op_name
makeRF_metric_op makeRF_module
makeRF_module core_metric_op glob_op_name
makeRF_metric_good_lemma makeRF_module
makeRF_invar_op makeRF_metric_op
core_metric_good_lemma;

Format.fprintf ppf 
"lemma %s :
  hoare [%s.init : true ==> %s (glob %s)].
proof.
rewrite /%s /=.
apply %s.
 qed.
 "
makeRF_init_invar_lemma
makeRF_module makeRF_invar_op makeRF_module
makeRF_invar_op
makeRF_core_init_invar_lemma;

Format.fprintf ppf
"
lemma %s (n : int) :
  hoare
  [%s.invoke :
   %s (glob %s) /\\ %s (glob %s) = n ==>
   %s (glob %s) /\\
 (res <> None => %s (glob %s) < n
 /\\ ((oget res).`1 = Adv => (oget res).`2.`2 \\in  adv_pis_rf_info rf_info))].
proof.
rewrite /%s /%s /=.
apply %s.
 qed.@]@;@;"

makeRF_invoke_lemma
makeRF_module
makeRF_invar_op makeRF_module makeRF_metric_op makeRF_module
makeRF_invar_op makeRF_module
makeRF_metric_op makeRF_module
makeRF_invar_op makeRF_metric_op
makeRF_core_invoke_lemma
  in
  print_cloneRF;
  let rp_module = (moduleRP id rfbt) in
  print_MakeRF_and_lemmas
    gvil.gvil_RP
    rp_module
    _RFRP
    (invarIRP rfbt true None)
    (initIRP rfbt true None)
    (metric_name_IRP rfbt true None)
    (invokeIRP rfbt true None)
    (metric_goodIRP rfbt true None);
  if IdMap.cardinal rfbt.params = 0
  then ()
  else
    let ip_module = (moduleIP id) in
    print_MakeRF_and_lemmas
    gvil.gvil_IP
    ip_module
    _RFIP
    (invarIRP rfbt false None)
    (initIRP rfbt false None)
    (metric_name_IRP rfbt false None)
    (invokeIRP rfbt false None)
    (metric_goodIRP rfbt false None)


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

    
let print_module_lemmas ?(rest_idx = None)
      (id : string) (root : string)
      (mbmap : message_body_tyd SLMap.t) (dii : symb_pair IdMap.t)
      (gvil : gvil) 
      (ppf : Format.formatter) (rfbt : real_fun_body_tyd)
    : unit =
  let ridx() = EcUtils.oget rest_idx in
  let parties = rfbt.parties in
  let ptns = fst (List.split (IdMap.bindings parties)) in
  let pmns = indexed_map_to_list_only_keep_keys rfbt.params in
  let pmns = if rest_idx = None
             then pmns
             else List.filteri (fun i _ -> i+1<>ridx())
                    pmns in
  let rpmns = List.map (fun pmn -> module_name_RF pmn) pmns in
  let ipmns = List.map (fun pmn -> module_name_IF pmn) pmns in
  let sfns = fst (List.split (IdMap.bindings rfbt.sub_funs)) in
  let module_name = if rest_idx = None
                    then module_name id
                    else rest_name id (ridx()) in
  let adv_pis = if rest_idx = None
                then "adv_pis_rf_info "^rf_info
                else (rest_composition_clone (ridx()))^".rest_adv_pis" in
  let party_invoke_lemma_name pn =
    if rest_idx = None
    then _invoke_pn pn
    else _invoke_pn_rest pn (ridx())
  in
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
        (party_invoke_lemma_name pn) print_lemma_params pmns;
      Format.fprintf ppf
        "@[%s.%s :@ %s (%s(glob %s)) = n@ ==>@ (res <> None =>@ %s (%s(glob %s)) < n@]@;"
        (module_name^(module_params_string pmns)) (proc_party_str pn)
        metric_name globop (uc_name id) 
        metric_name globop (uc_name id);
      Format.fprintf ppf
        "@[ /\\ ((oget res).`1 = %s => (oget res).`2.`2 \\in  %s))@]"
        mode_Adv adv_pis;
      Format.fprintf ppf "@]@;].@;";
      Format.fprintf ppf
        "@[proof. rewrite /%s /=. proc. inline. (*inline procedure calls*)@]@;"
        metric_name;
      print_proof_state_match root mbmap dii IdPairMap.empty "" ppf st_map;
      Format.fprintf ppf "@[qed.@]@;"
    in
    let print_party_metric_good ppf () =
      Format.fprintf ppf "@[lemma %s (g : %s) :@]@;"
        lemma_pt_metric_good_name stn;
      Format.fprintf ppf "@[  %s g => 0 <= %s g.@]@;" invar_op_name metric_name;
      Format.fprintf ppf "@[    proof. rewrite /%s /=.@]@;" metric_name;
      Format.fprintf ppf "@[      smt(). qed.@]@;";
    in
    let pt_glob_op_name =  glob_op_name (uc_name id) svn in
    if rest_idx = None
    then begin
      let svi = IdMap.find pn svim in
      Format.fprintf ppf "@[op %s (g : glob %s) / : %s = g.`%i.@]@;@;"
        pt_glob_op_name module_name stn svi;
      Format.fprintf ppf "@[%a@]@;@;"
        (print_party_state_metric metric_name stn snf)
      st_map
      end
    ;
    Format.fprintf ppf
      "@[%a@]@;@;" print_Pt_lemma_metric_invoke pt_glob_op_name;
    if rest_idx = None
    then begin
      Format.fprintf ppf "@[op %s (g : %s) : bool = predT g.@]@;@;"
        invar_op_name stn;
      Format.fprintf ppf
        "@[<v>%a@]@;@;"  print_party_metric_good ()
    end
  in
  let print_module_abbrev (rp : bool) =
    let desc = if rest_idx = None
               then (if rp then "real" else "ideal")
               else "" in
    let pmns = if rest_idx = None
               then (if rp then rpmns else ipmns)
               else List.init (List.length pmns)
                      (fun i -> if (i+1)<ridx()
                                then List.nth ipmns i
                                else List.nth rpmns i) in
    Format.fprintf ppf "@[(*abbreviation for %s with %s parameters*)@]@;"
      module_name desc;
    Format.fprintf ppf "@[module %s = %s.@]@;@;" 
      (moduleIRP id rfbt rp rest_idx) (module_name^(module_params_string pmns))
  in
  let print_glob_operators (rp : bool) =
    let gvil = if rest_idx = None
               then (if rp then gvil.gvil_RP else gvil.gvil_IP)
               else List.nth gvil.gvil_Rest (ridx()-1) in
    Format.fprintf ppf "@[%a@]@;@;"
      (print_glob_operator (glob_op_name_own (moduleIRP id rfbt rp rest_idx))
         (moduleIRP id rfbt rp rest_idx) (uc_name id))
      (get_own_glob_range_of_real_fun_glob_core rfbt gvil);
    List.iteri (fun i pmn -> Format.fprintf ppf "@[%a@]@;@;"
      (print_glob_operator (glob_op_name (moduleIRP id rfbt rp rest_idx) (uc_name pmn))
         (moduleIRP id rfbt rp rest_idx) ((module_name_IRF rfbt rp rest_idx i) pmn))
      (get_glob_range_of_parameter gvil pmn)) pmns;
    if rest_idx = None && rp then begin 
    let ogrs = get_own_glob_ranges_of_real_fun rfbt gvil in
    List.iter (fun sfn -> Format.fprintf ppf "@[%a@]@;@;"
      (print_glob_operator (glob_op_name (uc_name id) (uc_name sfn))
         module_name (module_name_IF sfn))
      (IdMap.find sfn ogrs)) sfns
    end
  in
  let print_metric_operator (rp : bool) =
    Format.fprintf ppf "@[<v>";
    Format.fprintf ppf "@[ op [smt_opaque] %s (g : glob %s) : int =@]@;"
      (metric_name_IRP rfbt rp rest_idx) (moduleIRP id rfbt rp rest_idx);
    let is_first = ref true in
    let plus() = if !is_first then begin is_first:=false; " " end else "+"
    in
    List.iteri (fun i pmn -> let ucpmn = uc_name pmn in
        Format.fprintf ppf "@[%s%s.%s(%s g)@]@;"
          (plus()) ucpmn (metricIRF rfbt rp rest_idx i) (glob_op_name (moduleIRP id rfbt rp rest_idx) ucpmn)
      ) pmns;
    List.iter (fun ptn ->  Format.fprintf ppf "@[%s%s(%s (%s g))@]@;"
          (plus()) (uc_party_metric_name ptn)
          (glob_op_name (uc_name id) (st_name ptn))
          (glob_op_name_own (moduleIRP id rfbt rp rest_idx))
    ) ptns;
    List.iter (fun sfn -> let ucsfn = uc_name sfn in
        Format.fprintf ppf "@[%s%s.%s(%s (%s g))@]@;"
          (plus()) ucsfn _metric_IF (glob_op_name (uc_name id) ucsfn)
          (glob_op_name_own (moduleIRP id rfbt rp rest_idx))
    ) sfns;
    Format.fprintf ppf ".@]@;@;"
  in
  let print_invoke_lemma (rp : bool) =
    let print_call_sub_invoke metric globop1 globop2 sub_invoke sub_invoke_pms smt_hint =
      Format.fprintf ppf "@[  if.@]@;";
      Format.fprintf ppf "@[  exlim (%s(%s(%s(glob %s)))) => _sub_metric.@]@;"
        metric globop1 globop2 (moduleIRP id rfbt rp rest_idx);
      Format.fprintf ppf "@[  call (%s _sub_metric %s).@]@;"
        sub_invoke sub_invoke_pms;
      Format.fprintf ppf "@[  skip.@]@;";
      Format.fprintf ppf "@[  smt(%s).@]@;" smt_hint;
    in
    Format.fprintf ppf "@[<v>";
    Format.fprintf ppf "@[lemma %s (n : int)  : hoare [@]@;" (invokeIRP rfbt rp rest_idx);
    Format.fprintf ppf "@[  %s.%s :@]@;" (moduleIRP id rfbt rp rest_idx) invoke;
    Format.fprintf ppf "@[  %s (glob %s) = n@]@;"
    (metric_name_IRP rfbt rp rest_idx) (moduleIRP id rfbt rp rest_idx);
    Format.fprintf ppf "@[  ==>@]@;";
    Format.fprintf ppf "@[  (res <> None =>@]@;";
    Format.fprintf ppf "@[  %s (glob %s) < n@]@;"
    (metric_name_IRP rfbt rp rest_idx) (moduleIRP id rfbt rp rest_idx);
    Format.fprintf ppf "@[/\\ ((oget res).`1 = Adv => (oget res).`2.`2 \\in  %s))].@]@;"
      adv_pis;
    Format.fprintf ppf "@[proof.@]@;";
    Format.fprintf ppf "@[rewrite /%s /=.@]@;" (metric_name_IRP rfbt rp rest_idx);
    Format.fprintf ppf "@[  proc.@]@;";
    Format.fprintf ppf "@[  sp 1.@]@;";
    List.iter (fun sfn ->
        let ucsfn = uc_name sfn in
        let metric = ucsfn^"."^_metric_IF in
        let globop1 = glob_op_name (uc_name id) ucsfn in
        let globop2 = glob_op_name_own (moduleIRP id rfbt rp rest_idx) in
        let sub_invoke = ucsfn^"."^iF_invoke in
        let sub_invoke_pms = "" in
        print_call_sub_invoke metric globop1 globop2 sub_invoke sub_invoke_pms smt_invoke_lemmas 
      ) sfns;
    List.iteri (fun i pmn ->
        let ucpmn = uc_name pmn in
        let metric = ucpmn^"."^(metricIRF rfbt rp rest_idx i) in
        let globop1 = glob_op_name (moduleIRP id rfbt rp rest_idx) ucpmn in
        let globop2 = "" in
        let sub_invoke = ucpmn^"."^(invokeIRF rfbt rp rest_idx i) in
        let sub_invoke_pms = "" in
        print_call_sub_invoke metric globop1 globop2 sub_invoke sub_invoke_pms smt_invoke_lemmas
      ) pmns;
    List.iter (fun ptn ->
        let pmns = match rest_idx with
          | None -> if rp
                    then rpmns
                    else ipmns
          | Some idx -> List.init ((IdMap.cardinal rfbt.params)-1)
                          (fun i -> if i+1<idx
                                    then List.nth ipmns i
                                    else List.nth rpmns i) in
        let metric = uc_party_metric_name ptn in
        let globop1 = glob_op_name (uc_name id) (st_name ptn) in
        let globop2 = glob_op_name_own (moduleIRP id rfbt rp rest_idx) in
        let sub_invoke = (party_invoke_lemma_name ptn) in
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
      (invarIRP rfbt rp rest_idx) (moduleIRP id rfbt rp rest_idx);
    let is_first = ref true in
    let cnj() = if !is_first then begin is_first:=false; "  " end else "/\\"
    in
    List.iteri (fun i pmn -> let ucpmn = uc_name pmn in
        Format.fprintf ppf "@[%s%s.%s(%s g)@]@;"
          (cnj()) ucpmn (invarIRF rfbt rp rest_idx i)
          (glob_op_name (moduleIRP id rfbt rp rest_idx) ucpmn)
      ) pmns;
    List.iter (fun ptn ->  Format.fprintf ppf "@[%s%s(%s (%s g))@]@;"
          (cnj()) (invar_pt_op_name ptn)
          (glob_op_name (uc_name id) (st_name ptn))
          (glob_op_name_own (moduleIRP id rfbt rp rest_idx))
    ) ptns;
    List.iter (fun sfn -> let ucsfn = uc_name sfn in
        Format.fprintf ppf "@[%s%s.%s(%s (%s g))@]@;"
          (cnj()) ucsfn _invar_IF
          (glob_op_name (uc_name id) ucsfn)
          (glob_op_name_own (moduleIRP id rfbt rp rest_idx))
    ) sfns;
    Format.fprintf ppf ".@]@;@;"
  in
  let print_metric_good_lemma (rp : bool) =
    Format.fprintf ppf "@[<v>";
    Format.fprintf ppf "@[lemma %s (g : glob %s) :@]@;"
    (metric_goodIRP rfbt rp rest_idx) (moduleIRP id rfbt rp rest_idx);
    Format.fprintf ppf "@[%s g => 0 <= %s g.@]@;"
      (invarIRP rfbt rp rest_idx) (metric_name_IRP rfbt rp rest_idx);
    Format.fprintf ppf "@[proof.@]@;";
    Format.fprintf ppf "@[rewrite /%s /=.@]@;"
      (metric_name_IRP rfbt rp rest_idx);
    Format.fprintf ppf "@[rewrite /%s /=.@]@;"
      (invarIRP rfbt rp rest_idx);
    Format.fprintf ppf "@[smt(@]@;";
    List.iteri(fun i pmn ->
        Format.fprintf ppf "@[%s.%s@]@;"
          (uc_name pmn) (metric_goodIRF rfbt rp rest_idx i)
      ) pmns;
    List.iter(fun sfn ->
        Format.fprintf ppf "@[%s.%s@]@;" (uc_name sfn) iF_metric_good
      ) sfns;
    List.iter(fun ptn ->
        Format.fprintf ppf "@[%s@]@;" (_metric_pt_good ptn)
      ) ptns;
    Format.fprintf ppf "@[).@]@;";
    Format.fprintf ppf "qed.@]@;@;"
  in
  let print_init_lemma (rp : bool) =
    Format.fprintf ppf "@[<v>";
    Format.fprintf ppf "@[lemma %s :@]@;" (initIRP rfbt rp rest_idx);
    Format.fprintf ppf "@[hoare [ %s.%s : true ==> %s (glob %s)].@]@;"
      (moduleIRP id rfbt rp rest_idx) init
      (invarIRP rfbt rp rest_idx) (moduleIRP id rfbt rp rest_idx);
    Format.fprintf ppf "@[proof. proc. sp. wp.@]@;";
    let pmnum = IdMap.cardinal rfbt.params in
    for i = pmnum-1 downto 0 do
      match rest_idx with
      | None -> if rp
                  then Format.fprintf ppf "@[call (%s.%s).@]@;"
                         (uc_name (List.nth pmns i)) rFRP_init
                  else Format.fprintf ppf "@[call (%s.%s).@]@;"
                         (uc_name (List.nth pmns i)) iF_init
      | Some r -> if (i + 1) < r
                    then Format.fprintf ppf "@[call (%s.%s).@]@;"
                         (uc_name (List.nth pmns i)) iF_init
                    else
                      if (i + 1) > r
                      then Format.fprintf ppf "@[call (%s.%s).@]@;"
                           (uc_name (List.nth pmns (i-1))) rFRP_init
                      else ()
    done;
    List.iter(fun sfn ->
        Format.fprintf ppf "@[call (%s.%s).@]@;"
          (uc_name sfn) iF_init
      ) (List.rev sfns);
    Format.fprintf ppf "@[skip.@]@;";
    Format.fprintf ppf "@[rewrite /%s /=.@]@;"
      (invarIRP rfbt rp rest_idx);
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
  if rest_idx = None
  then begin
    if IdMap.is_empty rfbt.params
    then print_it true
    else begin
        print_module_abbrev true;
        print_it true;
        print_module_abbrev false;
        print_it false;
      end
    end
  else begin
    if IdMap.cardinal rfbt.params > 1
    then print_module_abbrev true
    else ()
  ;
    print_it true
    end

let print_clone_Composition ppf (rest_idx : int) : unit =
  Format.fprintf ppf "
clone UC_Composition.Composition as %s with
op change_pari = %i,
op %s <- %s
proof *.
realize rf_info_valid. smt(%s). qed.
realize change_pari_valid. smt(). qed.
"
    (rest_composition_clone rest_idx)
    rest_idx
    rf_info rf_info
    adv_pi_begin_gt0_axiom_name
  
let print_CompEnv_abbrev id rfbt ppf rest_idx =
      Format.fprintf ppf
"(*abbreviation for %i. composed environment*)
module %s%i(Env : ENV) = %s.CompEnv(%s,Env).
 "
rest_idx
_COMPENV rest_idx
(rest_composition_clone rest_idx) (rest_nameP id rfbt rest_idx)


let print_sequence_of_games_proof  (id : string) ppf
       (rfbt : real_fun_body_tyd) =
  let pmnum = IdMap.cardinal rfbt.params in
  let mRP = moduleRP id rfbt in
  let _RFRP_Comp_RP_eq_lemma = "equiv_"^mRP^"_Composed1_RP" in
  let pmns = indexed_map_to_list_only_keep_keys rfbt.params in
  let ith_param_real i = module_name_RF (List.nth pmns (i-1)) in
  let ith_param_ideal i = module_name_IF (List.nth pmns (i-1)) in
  let _Comp_RP_Comp_IP_diff_lemma i =
    let _i = string_of_int i in
    "diff_Composed"^_i^"_RP_Composed"^_i^"_IP" in
  let _Comp_IP_Comp_RP_eq_lemma i =
    "equiv_Composed"^(string_of_int i)^"_IP_Composed"^(string_of_int (i+1))^"_RP" in
  let _Comp_IP_RFIP_eq_lemma =
    "equiv_Composed"^(string_of_int (IdMap.cardinal rfbt.params))^"_IP_RFIP" in
  let sim_st = sim_stack rfbt pmnum in
  let composition_module ((i, ri) : int * bool) : string =
    let ith_param = if ri
                    then ith_param_real i
                    else ith_param_ideal i
    in
    Printf.sprintf "%s.MakeRFComp(%s, %s)"
      (rest_composition_clone i)
      (parametrized_rest_module id rfbt i)
      ith_param
  in
  let print_RFRP_Comp_RP_eq_lemma ppf () =
    let print_exper_RFRP_prob ppf () =
      Format.fprintf ppf
        "Pr[Exper(MI(RFRP,Adv), Env).main(func', in_guard') %s &m : res]"
        "@"
    in 
    let print_exper_Rest1_RP_prob ppf () =
      Format.fprintf ppf
        "Pr[Exper(MI(%s, Adv), Env).main(func', in_guard') %s &m : res]"
        (composition_module (1,true)) "@"
    in 
    let print_exper_prob_diff ppf () =
      Format.fprintf ppf "`|%a@;-@;%a| <= 0.0"
        print_exper_RFRP_prob () print_exper_Rest1_RP_prob ()
    in
    let print_invariant ppf invstr =
      let print_param_globs ppf () =
        for i = 1 to IdMap.cardinal rfbt.params
        do
          Format.fprintf ppf "glob %s,\n" (ith_param_real i)
        done           
      in
      Format.fprintf ppf "={%s
glob Adv,
glob MI,
%aglob %s
}
/\\ RFCore.MakeRF.self{1} = UC_Composition.CompGlobs.mrfc_self{2}
/\\ %s._self{1} =  UC_Composition.CompGlobs.mrfc_self{2}"
        invstr
        print_param_globs ()(uc_name id)
        (uc_name id)
    in
    Format.fprintf ppf
"lemma %s
    (Env <: ENV{-MI, -RFRP, -AllCGs_})
    (Adv <: ADV{-MI, -Env,  -RFRP, -AllCGs_})
    (func' : addr, in_guard' : int fset) &m :
  %a
 .@;@;"
_RFRP_Comp_RP_eq_lemma
print_exper_prob_diff ();
    Format.fprintf ppf  "proof.@;@;";
    Format.fprintf ppf
"
(*change the goal to equal probabilities in order to apply byequiv*)
have H:
(
%a
)
    <=>
(
%a
 =
%a
).
smt().

apply H.
clear H.
@;"
print_exper_prob_diff ()
print_exper_RFRP_prob ()
print_exper_Rest1_RP_prob ();
    
    Format.fprintf ppf  "byequiv => //.@;@;";
    Format.fprintf ppf
"
(*unfold Exper main procedures, put in precondition all up to Adv.init call*)
proc.
inline *.
sp.
@; 
 ";
    Format.fprintf ppf
      "
(*Adv init call doesn't touch any of the globs, because of module restrictions*)
seq 1 1 : (%a).
call (_ : true).
skip.
move => />.
       "     print_invariant "func, in_guard, glob Env,";
    Format.fprintf ppf
      "
(*calling ENV main doesn't make a difference in globs between left and right side*)
call (_ : %a
  ); last first.
skip; move => />.
       @;" print_invariant "";
    Format.fprintf ppf
"(*unfold MI invoke to show the result is the same on both sides*)
proc.

  (*if m is not in inguard the result is the same on both sides*)
if; last first.
sp.
skip.
move => />.
move => />.

(*if m is in inguard the loop will return the same on both sides*) 
      inline loop.
(* on both sides before the while loop we have:
m0 <- m                                              
r0 <- None     
not_done <- true
      
and after the loop
r <- r0
*)
sp.
wp.
 @;";
    Format.fprintf ppf
"(*the locals and globals are the same after each iteration of the while loop*)
while (%a); last first.
 skip; move => />.
 @;"
    print_invariant "r0, m, m0, not_done,";
    Format.fprintf ppf
"(*case when (MakeInt.MI.func <= m0.`2.`1) is false is similar on both sides*)
if; last first.
sim.
move => />.
 @;";
    Format.fprintf ppf
"(*case when (MakeInt.MI.func <= m0.`2.`1) is true,
if calling invoke has the same result, the rest is similar on both sides*)
seq 1 1 : (%a); last first.
sim.
 @;" print_invariant "r0, m, m0, not_done,";
    Format.fprintf ppf
"(*show that MakeRF and MakeRFComp invoke have the same result*)
inline invoke.
sp.

(*the if conditions are the same, testing if real functionality is the
  destination m, in case it is not the destination the results are the same*)
if; last first.
sp. skip.
move => />.
move => />.
wp.
 
(*in case real functionality is the destination of m,
  the loops return the same result*)
inline loop.
sp.
wp.
 @;";
    Format.fprintf ppf
"(*each iteration of the wile loop has same result on both sides*)  
while (%a
); last first.
 skip. move => />.
 @;" print_invariant "r0, r1, r2, m, m0, m1, m2, not_done, not_done0,";
    Format.fprintf ppf
"(*we inline real functionality invoke and composed functionality invoke
to show the result is the same*)
inline{1} (1) invoke. 
inline %s.invoke.
sp 2 0.
 @;" (parametrized_rest_module id rfbt 1);
    Format.fprintf ppf
"(*case when message is for the first parameter functionality*)
 case (UC_Composition.CompGlobs.mrfc_self{2} ++ [UC__Rest1.change_pari] <= m2{2}.`2.`1).
@;";
    for i = 1 to IdMap.cardinal rfbt.sub_funs
    do
      Format.fprintf ppf
      "(*the message is not for %i. sub-functionality*)
rcondf{1} 0.
move => &m0.
skip.
move => />.
smt(not_le_other_branch).
       @;" i
    done;
    Format.fprintf ppf
"(*the if conditions on both sides are equivalent and true, and result is the same*)
rcondt{1} 0.
move => &m0.
skip.
move => />.

rcondt{2} 0.
move => &m0.
skip.
move => />.

sim.

(*case when message is NOT for the first parameter*)
(*message is NOT for the first parameter on right side*)
    rcondf {2} 0.
move => &m0.
skip.
move => />.
sp 0 2.
 @;";
    for i = 1 to IdMap.cardinal rfbt.sub_funs
    do
      Format.fprintf ppf
        "(*if m is for %i. sub-functionality*)
if.
move => />.
sim.
@;" i
    done;  
    Format.fprintf ppf
"(*message is NOT for the first parameter on left side*)
rcondf{1} 1.
move => &m0.
skip.
move => />.

(*the rest is similar*)
 sim.
 @;";
    Format.fprintf ppf  "qed.@;@;"
  in

  let print_simulator_abbrev ppf () =
    Format.fprintf ppf "@[<v>@[(*Simulator stack abreviation*)@]@;";
    Format.fprintf ppf "@[module %s(%s : ADV) = %s.@]@]" simip _Adv sim_st
  in
  let print_AllCGs_abbrev ppf () =
    Format.fprintf ppf
   "@[<v>@[(*all CompGlobs module, abreviation for lemma module restrictions*)@]@;";
    Format.fprintf ppf "@[module AllCGs_ = {@]@;";
    Format.fprintf ppf "@[module OwnCGs = UC_Composition.CompGlobs@]@;";
    List.iter (fun pmn ->
        Format.fprintf ppf "@[module %sAllCGs = %s.AllCGs@]@;"
               (uc_name pmn) (uc_name pmn);
      ) pmns;
    Format.fprintf ppf "}.@]@;@;"
  in
  let print_AllIFs_abbrev ppf () =
    Format.fprintf ppf
   "@[<v>@[(*all IFs module, abreviation for lemma module restrictions*)@]@;";
    Format.fprintf ppf "@[module AllIFs = {@]@;";
    Format.fprintf ppf "@[module OwnIF = IF@]@;";
    List.iter (fun pmn ->
        Format.fprintf ppf "@[module %sAllIFs = %s.AllIFs@]@;"
          (uc_name pmn) (uc_name pmn);
      ) pmns;
    Format.fprintf ppf "}.@]@;@;"
  in
  let print_Comp_RP_Comp_IP_diff_lemma ppf (i : int) =
    let pmth = uc_name (List.nth pmns (i-1)) in
    Format.fprintf ppf
"lemma %s
    (Env <: ENV{-MI,  -AllCGs_, -RFRP, -SIMIP, -AllIFs})
    (Adv <: ADV{-MI, -AllCGs_, -Env,  -RFRP, -SIMIP, -AllIFs})
    (func' : addr, in_guard' : int fset) &m :
    exper_pre func' =>
    disjoint in_guard' (adv_pis_rf_info rf_info) =>
`|Pr[Exper(MI(%s, %s), Env).main(func', in_guard') %s &m : res]
  -
Pr[Exper(MI(%s, %s), Env).main(func', in_guard') %s &m : res]|
  <=
%a
 .@;"
(_Comp_RP_Comp_IP_diff_lemma i)
(composition_module (i,true)) (sim_stack rfbt (i-1)) "@"
(composition_module (i,false)) (sim_stack rfbt i) "@"
(probability_parameter_Bound rfbt) i
;
  Format.fprintf ppf
    "proof.
move => experpre disjguard.
apply (%s.composition
Env (%s)
(%s) %s
(%s)
%s.IF
%s
%s
%s._invar_RFRP
%s._metric_RFRP
%s._invar_IF
%s._metric_IF
func' in_guard'
(%a)
&m).
     "
    (rest_composition_clone i)
    (parametrized_rest_module id rfbt i)
    (sim_stack rfbt (i-1)) (ith_param_real i)
    (sim_stack rfbt i)
    pmth
    (rest_invar i)
    (rest_metric i)
    pmth
    pmth
    pmth
    pmth
    (probability_parameter_Bound rfbt) i;
  Format.fprintf ppf "
apply %s.
apply %s.
apply %s.

apply %s.RFRP_metric_good.
apply %s.RFRP_init.
apply %s.RFRP_invoke.

apply %s.IF_metric_good.
apply %s.IF_init.
move => n.
conseq (%s.IF_invoke n).
smt(mem_oflist mem_rangeset).
trivial.
"
    (rest_metric_good i)
    (rest_init i)
    (rest_invoke i)
    pmth
    pmth
    pmth
    pmth
    pmth
    pmth;
  Format.fprintf ppf
"
smt(fsetUC %s.union_change_rest_eq_all_adv_pis_of_rf_info disjoint_with_union_implies_disjoint_with_first).
apply (%s.%s_RFRP_IF_advantage
    (%s(Env))
    (%s)
    (func' ++ [%s.change_pari])
  (in_guard' `|` %s.rest_adv_pis)
).
    by rewrite exper_pre_ext1.
by apply %s.disjoint_in_guard_with_all_implies_disjoint_add_rest_with_change. 
qed.@;@;"
    (rest_composition_clone i)
    pmth (fst (List.nth (indexed_map_to_list rfbt.params) (i-1)))
    (compenv i)
    (sim_stack rfbt (i-1))
    (rest_composition_clone i)
    (rest_composition_clone i)
    (rest_composition_clone i)
  in
  let print_Comp_IP_Comp_RP_eq_lemma ppf (i : int) =
    let print_exper_Resti_IP_prob ppf () =
      Format.fprintf ppf
        "Pr[Exper(MI(%s, Adv), Env).main(func', in_guard') %s &m : res]"
        (composition_module (i,false)) "@"
    in
    let print_exper_Restiinc_RP_prob ppf () =
      Format.fprintf ppf
        "Pr[Exper(MI(%s, Adv), Env).main(func', in_guard') %s &m : res]"
        (composition_module (i+1,true)) "@"
    in 
    let print_exper_prob_diff ppf () =
      Format.fprintf ppf "`|%a@;-@;%a| <= 0.0"
        print_exper_Resti_IP_prob () print_exper_Restiinc_RP_prob ()
    in
    let print_param_globs ppf () =
      for i = 1 to i
      do
        Format.fprintf ppf "glob %s,\n" (ith_param_ideal i)
      done;
      for i = (i+1) to pmnum
      do
        Format.fprintf ppf "glob %s,\n" (ith_param_real i)
      done     
    in
    let print_invariant_globs ppf invstr =
      Format.fprintf ppf "={%s
glob Adv,
glob MI,
%aglob %s
}"
        invstr
        print_param_globs ()(uc_name id)
    in
    let print_invariant_eqs ppf () =
      Format.fprintf ppf
"UC_Composition.CompGlobs.mrfc_self{1} = %s._self{1}
/\\ UC_Composition.CompGlobs.mrfc_self{2} = %s._self{2}"
(uc_name id)
(uc_name id)
    in
    let print_invariant ppf invstr =
      
      Format.fprintf ppf "%a
/\\ %a"
        print_invariant_globs invstr
        print_invariant_eqs ()
    in
    let print_sim_invariant ppf invstr =
      Format.fprintf ppf
        "(*both sides are similar*)
sim
/
(%a)
:
(%a).
@;"
      print_invariant_eqs ()
      print_invariant_globs invstr
    in
    Format.fprintf ppf
    "
lemma %s
(Env <: ENV{-MI,  -AllCGs_, -RFRP, -AllIFs})
(Adv <: ADV{-MI, -AllCGs_, -Env, -RFRP, -AllIFs})
(func' : addr, in_guard' : int fset) &m :
exper_pre func' =>
disjoint in_guard' (adv_pis_rf_info rf_info)  =>
%a
  <= 0.0
    .
     "
    (_Comp_IP_Comp_RP_eq_lemma i)
    print_exper_prob_diff ()
    ;
    Format.fprintf ppf  "proof.@;@;"
    ;
    Format.fprintf ppf
"move => exper_pre disjoint.
 @;"
    ;
    Format.fprintf ppf
"
(*change the goal to equal probabilities in order to apply byequiv*)
have H:
(
%a
)
    <=>
(
%a
 =
%a
).
smt().

apply H.
clear H.
@;"
print_exper_prob_diff ()
print_exper_Resti_IP_prob ()
print_exper_Restiinc_RP_prob ()
    ;
    Format.fprintf ppf
"byequiv => //.
proc.
@;"
    ;
    Format.fprintf ppf
"(*calling MI.init on both sides results in same memories*)
 seq 1 1 : (%a).
 @;"
    print_invariant "glob Env, func, in_guard,"
    ;
    Format.fprintf ppf
"(*inline all the inits before Adv.init*) 
inline *.
(*all init assignments before Adv.init go into precondition*)
sp.
%a
 @;" print_sim_invariant "glob Env, func, in_guard,"
    ;
    Format.fprintf ppf
"(*call Exper.main*)
call (_ :
%a
); last first.

skip.
move => />.
 @;" print_invariant ""
    ;
      Format.fprintf ppf
        "
(*unfold MI.invoke*)
proc.

(*if conditions are the same, as well as the else branches on both sides*)
if; last first.
sp. skip. move => />.
move => />.

(*inline MI.loop*)
inline loop.

(*everything before and after the while loop is the same, move it to pre/post conditions*)
sp.
wp.
@;"
    ;
    Format.fprintf ppf  
      "while (%a
); last first.
skip. move => />.
@;" print_invariant "r0, m, m0, not_done,"
    ;
    Format.fprintf ppf  
      "(*if conditions are the same on both sides, and else branches are similar*)
if; last first.
%a
move => />.
@;" print_sim_invariant "r0, m, m0, not_done,"
    ;
    Format.fprintf ppf  
      "(*after_func is similar on both sides*)
seq 1 1 : (%a
); last first.
%a
@;"
      print_invariant "r0, m, m0, not_done,"
      print_sim_invariant "r0, m, m0, not_done,"
    ;
    Format.fprintf ppf  
      "(*inline invoke, put everything before and after if into pre/post conditions*)
inline invoke.
sp. wp.

(*if conditions and else branches are the same on both sides*)
if; last first.
skip. move => />.
move => />.

(*inline composed RF loop, put everything before and after if into pre/post conditions*)
inline loop.
sp. wp.
@;"
    ;
      Format.fprintf ppf  
  "(*while invariant*)
while (%a
); last first.
skip. move => />.
@;" print_invariant "r0, r1, r2, m, m0, m1, m2, not_done, not_done0,"
    ;
    Format.fprintf ppf  
      "(*after_par_or_rest are similar on both sides*)
seq 1 1 : (%a
); last first.
%a
@;"
      print_invariant "r0, r1, r2, m, m0, m1, m2, not_done, not_done0,"
      print_sim_invariant "r0, r1, r2, m, m0, m1, m2, not_done, not_done0,"
    ;
    Format.fprintf ppf  
      "(*case when message is for the %i. parameter functionality*)
case (UC_Composition.CompGlobs.mrfc_self{1} ++ [%s.change_pari] <= m2{1}.`2.`1).
rcondt{1} 0.
move => &m0. skip. move => />.

(*message is not for right parameter functionality*)
rcondf{2} 0.
move => &m0. skip. move => />. smt(not_le_other_branch).

(*inline right invoke*)
inline{2} (1) invoke.
sp.
@;"
      i
      (rest_composition_clone i)
    ;
    for i = 1 to IdMap.cardinal rfbt.sub_funs
    do
      Format.fprintf ppf
      "(*the message is not for %i. sub-functionality*)
rcondf{2} 0.
move => &m0. skip. move => />. smt(not_le_other_branch).
       @;" i
    done
    ;
    for i = 1 to (i-1)
    do
      Format.fprintf ppf
      "(*the message is not for %i. parameter functionality*)
rcondf{2} 0.
move => &m0. skip. move => />. smt(not_le_other_branch).
       @;" i
    done
    ;
     Format.fprintf ppf
"(*message is for %i. parameter functionality*)
rcondt{2} 0.
move => &m0. skip. move => />.
%a
move => />.
 @;"
      i
      print_sim_invariant "r0, r1, r2, m, m0, m1, m2, not_done, not_done0,"
    ;
    Format.fprintf ppf  
      "(*case when message is NOT for the %i. parameter functionality*)
rcondf{1} 0.
move => &m0. skip. move => />.

(*case when message is for the %i. parameter functionality*)
case (UC_Composition.CompGlobs.mrfc_self{2} ++ [%s.change_pari] <= m2{2}.`2.`1).
rcondt{2} 0.
move => &m0. skip. move => />.

(*inline left invoke*)
inline{1} (1) invoke.
sp.
@;"
      i
      (i+1)
      (rest_composition_clone (i+1))
    ;
    for i = 1 to (i-1)
    do
      Format.fprintf ppf
      "(*the message is not for %i. parameter functionality*)
rcondf{1} 0.
move => &m0. skip. move => />. smt(not_le_other_branch).
       @;" i
    done
    ;
    for i = 1 to IdMap.cardinal rfbt.sub_funs
    do
      Format.fprintf ppf
      "(*the message is not for %i. sub-functionality*)
rcondf{1} 0.
move => &m0. skip. move => />. smt(not_le_other_branch).
       @;" i
    done
    ;
      Format.fprintf ppf
"(*message is for %i. parameter functionality*)
rcondt{1} 0.
move => &m0. skip. move => />.
%a
@;"
      (i+1)
      print_sim_invariant "r0, r1, r2, m, m0, m1, m2, not_done, not_done0,"
    ;
      Format.fprintf ppf
"(*case when message is NOT for the %i. parameter functionality*)
rcondf{2} 0.
move => &m0. skip. move => />.

(*inline both invokes*)
inline{1} (1) invoke.
inline{2} (1) invoke.
sp. wp.
 @;" (i+1)
    ;
    for i = 1 to IdMap.cardinal rfbt.sub_funs
    do
      Format.fprintf ppf
      "(*if message is for %i. sub-functionality*)
if. move => />. sim.
       @;" i
    done
    ;
    for i = 1 to (i-1)
    do
      Format.fprintf ppf
      "(*if message is for %i. parameter functionality*)
if. move => />. sim.
       @;" i
    done
    ;  
    Format.fprintf ppf  
  "
(*message is not for %i. parameter functionality*)
rcondf{2} 0.
move => &m0. skip. move => />.

(*message is not for %i. parameter functionality*)
rcondf{1} 0.
move => &m0. skip. move => />.

(*the rest is similar*)
sim.
@;" i (i+1)
    ;
    Format.fprintf ppf  "qed.@;@;"

  in
  let print_Comp_IP_RFIP_eq_lemma ppf () =
    let print_exper_Restl_RP_prob ppf () =
      Format.fprintf ppf
        "Pr[Exper(MI(%s, Adv), Env).main(func', in_guard') %s &m : res]"
        (composition_module (pmnum,false)) "@"
    in
    let print_exper_RFIP_prob ppf () =
      Format.fprintf ppf
        "Pr[Exper(MI(RFIP,Adv), Env).main(func', in_guard') %s &m : res]"
        "@"
    in 
    let print_exper_prob_diff ppf () =
      Format.fprintf ppf "`|%a@;-@;%a| <= 0.0"
        print_exper_Restl_RP_prob () print_exper_RFIP_prob ()
    in
    let print_invariant ppf invstr =
      let print_param_globs ppf () =
        for i = 1 to IdMap.cardinal rfbt.params
        do
          Format.fprintf ppf "glob %s,\n" (ith_param_ideal i)
        done           
      in
      Format.fprintf ppf "={%s
glob Adv,
glob MI,
%aglob %s
}
/\\ RFCore.MakeRF.self{1} = UC_Composition.CompGlobs.mrfc_self{2}
/\\ %s._self{1} =  UC_Composition.CompGlobs.mrfc_self{2}"
        invstr
        print_param_globs ()(uc_name id)
        (uc_name id)
    in
    Format.fprintf ppf
    "
lemma %s
(Env <: ENV{-MI, -AllCGs_, -RFIP})
(Adv <: ADV{-MI, -AllCGs_, -Env, -RFIP})
(func' : addr, in_guard' : int fset) &m :
exper_pre func' =>
disjoint in_guard' (adv_pis_rf_info rf_info)  =>
%a
.
@;"
      _Comp_IP_RFIP_eq_lemma
      print_exper_prob_diff ()
    ;
    Format.fprintf ppf "proof.@;@;";
    Format.fprintf ppf "move => exper_pre disjoint.";
    Format.fprintf ppf
"
(*change the goal to equal probabilities in order to apply byequiv*)
have H:
(
%a
)
    <=>
(
%a
 =
%a
).
smt().

apply H.
clear H.
@;"
print_exper_prob_diff ()
print_exper_RFIP_prob ()
print_exper_Restl_RP_prob ();
    
    Format.fprintf ppf  "byequiv => //.@;@;";
    Format.fprintf ppf
"
(*unfold Exper main procedures, put in precondition all up to Adv.init call*)
proc.
@; 
 "
    ;
    Format.fprintf ppf
"(*calling MI.init on both sides results in same memories*)
   seq 1 1 : (%a
).
(*inline all the inits before Adv.init*) 
inline *.
(*all init assignments before Adv.init go into precondition*)
sp.
(*calling Adv.init is similar on both sides*)
sim.
 @;"
print_invariant "glob Env, func, in_guard,"
    ;
    Format.fprintf ppf
"(*call Exper.main*)
call (_ : %a
); last first.
skip. move => />.
 @;"
print_invariant ""
    ;
    Format.fprintf ppf
"(*unfold MI.invoke*)
proc.

(*if conditions and else branches are the same on both sides*)
if; last first.
sp. skip. move => />.
move => />.

(*inline MI.loop on both sides*)
inline loop.

(*put all before and after while loop into pre and post conditions*)
sp.
wp.
@;"
    ;
    Format.fprintf ppf
"while (%a); last first.
skip. move => />.
@;"
print_invariant "r0, m, m0, not_done,"
    ;
      Format.fprintf ppf
"(*if message destination sub-address of MI.func, prove else branch first, they are same*)
if; last first.
sim.
move => />.

(*inline invoke on both sides*)
inline{1} (1) invoke.
inline{2} (1) invoke.
sp.

(*if conditions and else branches are same on both sides*)
if; last first.
sim.
move => />.

(*inline loop on both sides*)
inline loop.
 sp.
 @;"
    ;
    Format.fprintf ppf
"(*calls after while loop are similar*)
seq 1 1 : (%a); last first.
sp.
sim.
 @;"
print_invariant "m,m0,m1,m2,r0,r1,r2,not_done, not_done0,"
    ;
      Format.fprintf ppf
"(*while invariant*)
while (%a); last first.
skip. move => />.
@;"
      print_invariant "m,m0,m1,m2,r0,r1,r2,not_done, not_done0,"
    ;
      Format.fprintf ppf
"(*case when message is for 2. parameter functionality*)
case (UC_Composition.CompGlobs.mrfc_self{2} ++ [%s.change_pari] <= m2{2}.`2.`1).
rcondt{2} 0.
move => &m0. skip. move => />.

(*inline real functionality invoke*)
inline{1} (1) invoke.
 sp.
 @;"
        (rest_composition_clone pmnum)
    ;
    for i = 1 to IdMap.cardinal rfbt.sub_funs
    do
      Format.fprintf ppf
      "(*the message is not for %i. sub-functionality*)
rcondf{1} 0.
move => &m0. skip. move => />. smt(not_le_other_branch).
       @;" i
    done
    ;
    for i = 1 to (pmnum-1)
    do
      Format.fprintf ppf
      "(*the message is not for %i. parameter functionality*)
rcondf{1} 0.
move => &m0. skip. move => />. smt(not_le_other_branch).
       @;" i
    done
    ;
     Format.fprintf ppf
"(*message is for %i. parameter functionality*)
rcondt{1} 0.
move => &m0. skip. move => />.
@;" pmnum
    ;
    Format.fprintf ppf
"(*the rest is similar*)
sim.
 @;"
    ;
      Format.fprintf ppf
"(*case when message is NOT for %i. parameter functionality*)
rcondf{2} 0.
move => &m0. skip. move => />.

(*inline both invoke calls*)
inline{1} (1) invoke.
inline{2} (1) invoke.
sp.
@;" pmnum
    ;
    for i = 1 to IdMap.cardinal rfbt.sub_funs
    do
      Format.fprintf ppf
      "(*if message is for %i. sub-functionality*)
if. move => />. sim.
       @;" i
    done
    ;
    for i = 1 to (pmnum-1)
    do
      Format.fprintf ppf
      "(*if message is for %i. parameter functionality*)
if. move => />. sim.
       @;" i
    done
    ;  
    Format.fprintf ppf
"
(*message is not for %i. parameter functionality*)
rcondf{1} 0.
move => &m0. skip. move => />.

(*the rest is similar*)
sim.
 @;" pmnum
    ;
    Format.fprintf ppf "qed.@;@;"

  in
  let print_RFRP_RFIP_diff_lemma ppf () =
    (*lemma statement*)
    Format.fprintf ppf
    "
     lemma exper_RF_RP_IP_Pr_diff
(Env <: ENV{-MI, -AllIFs, -RFRP, -AllCGs_, -SIMIP})
    (Adv <: ADV{-MI, -Env, -AllIFs, -RFRP, -AllCGs_, -SIMIP})
    (func' : addr, in_guard' : int fset) &m :
    exper_pre func' =>
    disjoint in_guard' (adv_pis_rf_info rf_info) =>
  `|Pr[Exper(MI(RFRP,Adv), Env).main(func', in_guard') %s &m : res]
-
    Pr[Exper(MI(RFIP,SIMIP(Adv)), Env).main(func', in_guard') %s &m : res]| <=
 (
%a
     )
      .
     " "@" "@" (sum_of_prob_diffs rfbt) ()
    ;
      (*proof*)
    let apply_security_trans
      (mod1 : string) (mod2 : string) (mod3 : string)
      (adv1 : string) (adv2 : string) (adv3 : string)
      (bound1 : string) (bound2 : string) =
      Format.fprintf ppf "@[apply (
    MakeInt.security_trans
    (%s)
    (%s)
    (%s)
    (%s)
    (%s)
    (%s)

    Env
    func' in_guard'
    (%s)
    (%s)
    &m
). @]@;"
        mod1
        mod2
        mod3
        adv1
        adv2
        adv3
        bound1
        bound2
    in
    let by_apply (lemma : string) (adv : string) =
      Format.fprintf ppf
        "@[ by apply (%s Env (%s) func' in_guard' &m).@]@;@;"
        lemma adv
    in
    Format.fprintf ppf "@[<v>@[proof.@]@;";
    Format.fprintf ppf "@[move => exper disj.@]@;";
    let sum_bound : string = Format.asprintf "%a" (sum_of_prob_diffs rfbt) () in
    let simip_adv = simip^"("^_Adv^")" in
    apply_security_trans
      _RFRP (composition_module (1,true)) _RFIP
      _Adv _Adv simip_adv
      "0.0" sum_bound;
    by_apply _RFRP_Comp_RP_eq_lemma _Adv;
    for pn = 1 to pmnum do
      apply_security_trans
        (composition_module (pn,true)) (composition_module (pn,false)) _RFIP
        (sim_stack rfbt (pn-1)) (sim_stack rfbt pn) simip_adv
        (Format.asprintf "%a" (probability_parameter_Bound rfbt) pn)
        (Format.asprintf "%a" (sum_of_prob_diffs_from rfbt) (pn+1));
      by_apply (_Comp_RP_Comp_IP_diff_lemma pn) _Adv;
      if pn < pmnum
      then begin
          apply_security_trans
        (composition_module (pn,false)) (composition_module (pn+1,true)) _RFIP
        (sim_stack rfbt pn) (sim_stack rfbt pn) simip_adv
        "0.0" (Format.asprintf "%a" (sum_of_prob_diffs_from rfbt) (pn+1));
        by_apply (_Comp_IP_Comp_RP_eq_lemma pn) (sim_stack rfbt pn);
      end
    done
    ;
    by_apply _Comp_IP_RFIP_eq_lemma simip_adv;
    Format.fprintf ppf "qed.@]@;@;"
  in
  print_AllCGs_abbrev ppf ();
  print_AllIFs_abbrev ppf ();
  if pmnum = 0
  then ()
  else begin
    Format.fprintf ppf "@[<v>";
    Format.fprintf ppf "@[%a@]@;@;"
      print_RFRP_Comp_RP_eq_lemma ();
    Format.fprintf ppf "@[%a@]@;@;"
      print_simulator_abbrev ();
    for pn = 1 to pmnum do
      Format.fprintf ppf "@[%a@]@;@;"
        print_Comp_RP_Comp_IP_diff_lemma pn;
      if pn < pmnum
      then Format.fprintf ppf "@[%a@]@;@;"
             print_Comp_IP_Comp_RP_eq_lemma pn;
    done
    ;
    Format.fprintf ppf "@[%a@]@;@;"
      print_Comp_IP_RFIP_eq_lemma ();
    Format.fprintf ppf "@[%a@]@;@;"
      print_RFRP_RFIP_diff_lemma ();
    Format.fprintf ppf "@]"
  end
  


  
let gen_real_fun (sc : EcScope.scope) (root : string) (id : string)
      (mbmap : message_body_tyd SLMap.t) (rfbt : real_fun_body_tyd)
      (rapm : rf_addr_port_maps)
      (dii : symb_pair IdMap.t) (gvil : gvil): string =
  let sf = Format.get_str_formatter () in
  Format.fprintf sf "@[<v>";
  Format.fprintf sf "@[%a@]@;@;" print_rf_info_operator rfbt;
  Format.fprintf sf "@[%a@]@;@;" (print_addr_and_port_operators sc) rapm;
  Format.fprintf sf "@[%a@]@;@;" (print_party_types sc) rfbt.parties;
  Format.fprintf sf "@[%a@]@;@;" (print_real_module sc root id mbmap dii
                                    rapm.party_ext_port_id) rfbt;
  Format.fprintf sf "@[<v>%a@]@;@;"
    (print_module_lemmas id root mbmap dii gvil) rfbt;
  for i = 1 to IdMap.cardinal rfbt.params do
    Format.fprintf sf "@[%a@]@;@;"
      (print_rest_module sc root id mbmap dii rapm.party_ext_port_id rfbt) i;
    Format.fprintf sf "@[%a@]@;@;" print_clone_Composition i;
    Format.fprintf sf "@[<v>%a@]@;@;"
      (print_module_lemmas id root mbmap dii gvil ~rest_idx:(Some i)) rfbt;
    Format.fprintf sf "@[%a@]@;@;" (print_CompEnv_abbrev id rfbt) i
  done;
  Format.fprintf sf "@[<v>%a@]@;@;"   print_cloneRF_MakeRF (id,rfbt, gvil);
  Format.fprintf sf "@[%a@]@;@;" (print_sequence_of_games_proof id) rfbt;
  Format.fprintf sf "@]";
  Format.flush_str_formatter ()

let gen_fun (sc : EcScope.scope) (root : string) (id : string)
      (mbmap : message_body_tyd SLMap.t)
      (rapm : rf_addr_port_maps option) (ft : fun_tyd) (dii : symb_pair IdMap.t)
      (gvil : gvil): string =
  let fbt = EcLocation.unloc ft in
  match fbt with
  | FunBodyIdealTyd ifbt -> gen_ideal_fun sc root id mbmap ifbt dii
  | FunBodyRealTyd rfbt  -> gen_real_fun sc root id mbmap rfbt (EcUtils.oget rapm) dii gvil

let print_simulator_module (sc : EcScope.scope) (root : string) (id : string)
  (mbmap : message_body_tyd SLMap.t)
  (ais : symb_pair IdPairMap.t) (ppf : Format.formatter) (sbt : sim_body_tyd)
    : unit =
  let print_vars () =
    Format.fprintf ppf "@[var %s : %a option@]@;"
      if_addr_opt (pp_type sc) addr_ty;
     Format.fprintf ppf "@[var %s : %s@]@;" _st state_type_name_SIM;
  in
  let print_proc_init () =
    Format.fprintf ppf "@[proc init() : unit = {@]@;<0 2>@[<v>";
    Format.fprintf ppf "@[%s <- None; %s <- %s;@]@;"
      if_addr_opt _st (state_name_SIM (initial_state_id_of_states sbt.states));
    Format.fprintf ppf "@]@;@[}@]@;"
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
        ppf stid st.params mmc pfx msg_name mb state_name_SIM "";
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
    (state_name_SIM stid) print_state_params_names spnt;
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
  Format.fprintf ppf "@[module %s = {@]@;<0 2>@[<v>" (uc_name id);
  print_vars ();
  print_proc_init ();
  let sim_uses = Some sbt.uses in
  print_mmc_procs ~sim_uses
    sc root mbmap ppf sbt.states state_name_SIM IdMap.empty ais None "";
  print_proc_invoke ppf sbt.states;
  Format.fprintf ppf "@]@\n}.";
  ()
  
let print_cloneSIM_MS ppf (id,sbt : string * sim_body_tyd) =
  let print_cloneSIM =
  Format.fprintf ppf "@;@[clone Simulator as MSCore with@]@;";
  Format.fprintf ppf "@[op sim_adv_pi <- %s@]@;" adv_if_pi_op_name;
  Format.fprintf ppf "@[proof *.@]@;";
  Format.fprintf ppf "@[realize sim_adv_pi_ge1. smt(%s). qed.@]@;"
    adv_pi_begin_gt0_axiom_name
  in 
  let print_MS =
    Format.fprintf ppf
      "@[module SIM(%s : ADV) = MSCore.MS(%s, %s).@]"
      _Adv (uc_name id) _Adv
  in
  print_cloneSIM;
  print_MS

let print_state_type_SIM
      (sc : EcScope.scope)
      (ppf : Format.formatter)
      (states : state_tyd IdMap.t)
    : unit =
  print_state_type sc ppf states state_type_name_SIM state_name_SIM 

let gen_sim (sc : EcScope.scope) (root : string) (id : string)
      (mbmap : message_body_tyd SLMap.t) (sbt : sim_body_tyd)
      (ais : symb_pair IdPairMap.t): string =
  let sf = Format.get_str_formatter () in
  Format.fprintf sf "@[<v>";
  Format.fprintf sf "@[%a@]@;@;" (print_state_type_SIM sc) sbt.states;
  Format.fprintf sf "@[%a@]@;@;"
    (print_simulator_module sc root id mbmap ais) sbt;
    Format.fprintf sf "@[%a@]@;@;" print_SIM_invar id;
    Format.fprintf sf "%a" (print_SIM_metric id root mbmap ais) sbt.states;
  Format.fprintf sf "@[%a@]@;@;" print_SIM_metric_good_init_lemmas (uc_name id);
  Format.fprintf sf "@[<v>%a@]@;"   print_cloneSIM_MS (id,sbt);
  Format.fprintf sf "@]";
  Format.flush_str_formatter ()


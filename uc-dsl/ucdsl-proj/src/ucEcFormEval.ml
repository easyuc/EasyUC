open UcMessage

type eval_condition_result = 
  | Bool of bool
  | Undecided
(*  
let get_ttenv () =
  {
    EcHiGoal.tt_provers    = (fun _ -> {
      EcProvers.dft_prover_infos with pr_provers = EcProvers.dft_prover_names
      });
    EcHiGoal.tt_smtmode    = `Standard;
    EcHiGoal.tt_implicits  = true;
    EcHiGoal.tt_oldip      = false;
    EcHiGoal.tt_redlogic   = true;
    EcHiGoal.tt_und_delta  = false;
  }
 *) 
(* proof pretty printer*)
let pp_tc tc = (* copied from ecLowGoal.ml *)
  let pr = EcCoreGoal.proofenv_of_proof (EcCoreGoal.proof_of_tcenv tc) in
  let cl = List.map (fun h -> EcCoreGoal.FApi.get_pregoal_by_id h pr)
    (EcCoreGoal.FApi.tc_opened tc) in
  let cl = List.map (fun (x:EcCoreGoal.pregoal) 
    -> (EcEnv.LDecl.tohyps x.g_hyps, x.g_concl)) cl in

  match cl with [] -> () | hd :: tl ->

  Format.eprintf "%a@."
    (EcPrinting.pp_goal (EcPrinting.PPEnv.ofenv (EcCoreGoal.FApi.tc_env tc)) 
    {prpo_pr = true; prpo_po = true})
    (hd, `All tl)

let pp_proof (proof : EcCoreGoal.proof) : unit =
  pp_tc (EcCoreGoal.tcenv_of_proof proof)

(*comment out for printf debugging*)
let print_endline _ = ()
let pp_proof _ = ()
   
let run_tac (tac : EcCoreGoal.FApi.backward) (proof : EcCoreGoal.proof) 
: EcCoreGoal.proof =
  let tc1 = EcCoreGoal.tcenv1_of_proof proof in
  let tc = tac tc1 in
  let proof' = EcCoreGoal.proof_of_tcenv tc in
  pp_proof proof';
  proof'

let run_tacl (tacl : EcCoreGoal.FApi.backward list) (proof : EcCoreGoal.proof)
: EcCoreGoal.proof =
  List.fold_left (fun p tac -> run_tac tac p) proof tacl

(*move => />.*)
let crush (proof : EcCoreGoal.proof) : EcCoreGoal.proof =
  let intro1_crush = (*modified from ecHiGoal.ml*)
    let delta, tsolve = (true , None) in
    EcCoreGoal.FApi.t_or
      (EcPhlConseq.t_conseqauto ~delta ?tsolve)
      (EcLowGoal.t_crush ~delta ?tsolve)
  in
  print_endline "move => />.";
  run_tac intro1_crush proof

let move_hyp_form_to_concl 
(h_id : EcIdent.t) 
(proof : EcCoreGoal.proof) 
: EcCoreGoal.proof =
  let generalize_hyp = EcLowGoal.t_generalize_hyp ~clear:`Yes h_id in
  print_endline "move : H.";
  run_tac generalize_hyp proof

let get_only_pregoal (proof : EcCoreGoal.proof) : EcCoreGoal.pregoal =
  let goal = EcCoreGoal.opened proof in
  match goal with
  | Some (1, pregoal) -> pregoal
  | _ -> failwith "failed getting the one and only pregoal"
  
let move_all_hyp_forms_to_concl (proof : EcCoreGoal.proof) : EcCoreGoal.proof =
  let hyps = (get_only_pregoal proof).g_hyps  in
  let hyp_ids = List.filter_map ( fun h -> 
      match h with 
      | (id, EcBaseLogic.LD_hyp _) -> Some id
      | _ -> None
    ) (EcEnv.LDecl.tohyps hyps).h_local
  in
  let proof' = List.fold_right move_hyp_form_to_concl hyp_ids proof in
  proof'
(*  
let pp_prover_infos (pi : EcProvers.prover_infos) : unit =
  print_endline "SMT prover_infos BEGIN";
  print_endline ("pr_maxprocs="^(string_of_int pi.pr_maxprocs));
  print_endline "pr_provers:";
  List.iter (fun p -> print_endline p) pi.pr_provers;
  print_endline ("pr_timelimit="^(string_of_int pi.pr_timelimit));
  print_endline ("pr_cpufactor="^(string_of_int pi.pr_cpufactor));
  print_endline ("pr_quorum="^(string_of_int pi.pr_quorum));
  print_endline ("pr_verbose="^(string_of_int pi.pr_verbose));
  print_endline ("pr_all="^(string_of_bool pi.pr_all));
  print_endline ("pr_max="^(string_of_int pi.pr_max));
  print_endline ("pr_iterate="^(string_of_bool pi.pr_iterate));
  print_endline "SMT prover_infos END"
*)

let can_prove_smt (proof : EcCoreGoal.proof) (pi : EcProvers.prover_infos): bool =
  pp_proof proof;
  let pregoal = get_only_pregoal proof in
  try
    let b = EcSmt.check pi pregoal.g_hyps pregoal.g_concl in
    print_endline (match b with true -> "SMT true" | false -> "SMT false");
    b
  with _ ->
    print_endline "SMT exception";
    false

let can_prove_crush (proof : EcCoreGoal.proof) : bool =
  let proof_m = move_all_hyp_forms_to_concl proof in
  let proof_c = crush proof_m in
  EcCoreGoal.closed proof_c

let eval_condition_pre_tacs
(hyps : EcEnv.LDecl.hyps) 
(form : EcCoreFol.form)
(pi : EcProvers.prover_infos)
(pre_tacs : EcCoreGoal.FApi.backward list)
: eval_condition_result =
  let proof_true = EcCoreGoal.start hyps form in
  let proof_true = run_tacl pre_tacs proof_true in

  let proof_false = EcCoreGoal.start hyps (EcCoreFol.f_not form) in
  let proof_false = run_tacl pre_tacs proof_false in

  if can_prove_crush proof_true
  then Bool true
  else
    if can_prove_crush proof_false
    then Bool false
    else
      if can_prove_smt proof_true pi
      then Bool true
      else
        if can_prove_smt proof_false pi
        then Bool false
        else Undecided
      

let eval_condition 
(hyps : EcEnv.LDecl.hyps) 
(form : EcCoreFol.form)
(pi : EcProvers.prover_infos)
: eval_condition_result =
  eval_condition_pre_tacs hyps form pi []

let unique_id_for_proof (proof : EcCoreGoal.proof) : EcIdent.t = 
  let pregoal = get_only_pregoal proof in
  let hyps = pregoal.g_hyps in
  let name = EcUid.NameGen.ofint (EcUid.unique ()) in
  EcEnv.LDecl.fresh_id hyps name

(*move => [#].*)
let move_hash (proof : EcCoreGoal.proof) : EcCoreGoal.proof =
  let intro1_full_case tc (*modified from ecHiGoal.ml*)
  =
    let red = `NoDelta in

    let t_case =
      let t_and = fun tc -> ([2]   , EcLowGoal.t_elim_and ~reduce:red tc) in
      let ts = [t_and] in
      fun tc -> EcCoreGoal.FApi.t_or_map ts tc
    in

    let doit tc =
      let rec aux imax tc =
        if imax = Some 0 then EcLowGoal.t_id tc else

        try
          let ntop, tc = t_case tc in

          EcCoreGoal.FApi.t_sublasts
          (List.map (fun i tc -> aux (EcUtils.omap ((+) (i-1)) imax) tc) ntop)
            tc
        with EcCoreGoal.InvalidGoalShape ->
          try
            tc |> EcLowGoal.t_intro_sx_seq
              `Fresh
              (fun id ->
                EcCoreGoal.FApi.t_seq
                  (aux (EcUtils.omap ((+) (-1)) imax))
                  (EcLowGoal.t_generalize_hyps ~clear:`Yes [id]))
          with
          | EcCoreGoal.TcError _ when EcUtils.is_some imax ->
              EcCoreGoal.tc_error (EcCoreGoal.(!!) tc) 
              "not enough top-assumptions"
          | EcCoreGoal.TcError _ ->
              EcLowGoal.t_id tc
      in
      aux (Some 1) tc
    in
    doit tc
  in
  print_endline "move => [#].";
  run_tac intro1_full_case proof

(*move => hyp_name.*)    
let move_up (proof : EcCoreGoal.proof) : EcCoreGoal.proof =
  let intro1_core id tc = (*modified from ecHiGoal.ml*)
    EcLowGoal.t_intros [id] tc
  in
  let h_id = unique_id_for_proof proof in
  let h_id_mloc = EcUtils.Tagged (h_id,Some EcLocation._dummy) in
  print_endline "move => H.";
  run_tac (intro1_core h_id_mloc) proof

(*move => /=.*)
let move_simplify (proof : EcCoreGoal.proof) : EcCoreGoal.proof =
  let intro1_simplify tc = (*modified from ecHiGoal.ml*)
    EcLowGoal.t_simplify ~delta:`No ~logic:(Some `Full) tc
(* Alley: the other options for delta are
  type redmode = [`Force | `IfTransparent | `IfApplied]
  See EcEnv, module Op
*)

  in
  print_endline "move => /=.";
  run_tac intro1_simplify proof

let is_concl_p (proof : EcCoreGoal.proof) (p_id : EcIdent.t) : bool =
  let pregoal = get_only_pregoal proof in
  let concl = pregoal.g_concl in
  begin match (EcCoreFol.f_node concl) with
  | Fapp (f, _ ) -> 
    begin match (EcCoreFol.f_node f) with
    | Flocal id when id = p_id -> true
    | _ -> false
    end
  | _ -> false
  end
  
let extract_form (proof : EcCoreGoal.proof) (p_id : EcIdent.t) 
: EcCoreFol.form =
  let pregoal = get_only_pregoal proof in
  let concl = pregoal.g_concl in
  begin match (EcCoreFol.f_node concl) with
  | Fapp (f, [fs]) -> 
    begin match (EcCoreFol.f_node f) with
    | Flocal id when id = p_id -> fs
    | _ -> failwith "extract_form failed - not application of p_id"
    end
  | _ -> failwith "extract_form failed - not application"
  end

let progression 
(f : EcCoreGoal.proof -> EcCoreGoal.proof option)
(proof : EcCoreGoal.proof) : EcCoreGoal.proof option =
  let rec r 
  (first_call : bool) (proof : EcCoreGoal.proof) 
  : EcCoreGoal.proof option 
  = match f proof with
    | None -> 
      if first_call
      then None
      else Some proof
    | Some proof_new -> r false proof_new
  in
  r true proof
(*  
let move_hash_all (proof : EcCoreGoal.proof) (p_id : EcIdent.t) 
: EcCoreGoal.proof =
  let hash_step (proof : EcCoreGoal.proof) : EcCoreGoal.proof option =
    if (is_concl_p proof p_id)
    then
      None
    else
      let proof_a = try move_hash proof with _ -> proof in
      let proof_b = move_simplify proof_a in
      let proof_c = move_up proof_b in
      Some proof_c
   in
   let proof_o = progression hash_step proof in
   match proof_o with
   | None -> proof
   | Some pr -> pr
   

let prelims (proof : EcCoreGoal.proof) (p_id : EcIdent.t) : EcCoreGoal.proof =
  let proof_a = move_all_hyp_forms_to_concl proof in
  let proof_b = move_hash_all proof_a p_id in
  let proof_c = move_all_hyp_forms_to_concl proof_b in
  proof_c
*)
let intro1_rw s tc = (*modified from ecHiGoal.ml*)
  let process_rewrite1_core ?(close = true) s pt tc =
    let tc = EcHiGoal.LowRewrite.t_rewrite_r (s, None, None) pt tc in
    let cl = fun tc ->
      if EcFol.f_equal EcFol.f_true (EcCoreGoal.FApi.tc1_goal tc) then
        EcLowGoal.t_true tc
      else EcLowGoal.t_id tc
    in 
    if close then EcCoreGoal.FApi.t_last cl tc else tc
  in
  let h = EcIdent.create "_" in
  let rwt tc =
    let pt = 
    EcProofTerm.pt_of_hyp (EcCoreGoal.(!!) tc) (EcCoreGoal.FApi.tc1_hyps tc) h 
    in
    process_rewrite1_core ~close:false s pt tc
  in 
  EcCoreGoal.FApi.t_seqs 
  [EcLowGoal.t_intros_i [h]; rwt; EcLowGoal.t_clear h] tc

(*move => ->.*)  
let move_right (proof : EcCoreGoal.proof) : EcCoreGoal.proof =
  print_endline "move => ->.";
  run_tac (intro1_rw `LtoR) proof

(*move => <-.*)
let move_left (proof : EcCoreGoal.proof) : EcCoreGoal.proof =
  print_endline "move => <-.";
  run_tac (intro1_rw `RtoL) proof

let rec move_all_hyps_up (proof : EcCoreGoal.proof) (p_id : EcIdent.t) 
: EcCoreGoal.proof =
  if (is_concl_p proof p_id)
  then 
    proof
  else 
    let proof' = move_up proof in
    move_all_hyps_up proof' p_id

let count_hyp_forms (proof : EcCoreGoal.proof) (p_id : EcIdent.t) : int =
  print_endline "BEGIN count_hyp_forms";
  let proof' = move_all_hyps_up proof p_id in
  let pregoal = get_only_pregoal proof' in
  let h = (EcEnv.LDecl.tohyps pregoal.g_hyps).h_local in
  let h_forms = List.filter 
    (
      fun (_,l_k) -> 
        match l_k with 
        | EcBaseLogic.LD_hyp _ -> true 
        | _ -> false 
    ) h 
  in
  print_endline "END count_hyp_forms";
  List.length h_forms
  
let try_rewriting (proof : EcCoreGoal.proof) (p_id : EcIdent.t)
: EcCoreGoal.proof option =
  let move_right_simplify proof =
    let proof_a = move_right proof in
    let proof_b = move_simplify proof_a in
    Some proof_b
  in
  let move_left_simplify proof =
    let proof_a = move_left proof in
    let proof_b = move_simplify proof_a in
    Some proof_b
  in
  let go_left_first proof =
    let concl = (get_only_pregoal proof).g_concl in
    begin match EcFol.sform_of_form concl with
    | SFimp (h,_) ->
      begin match EcFol.sform_of_form h with
      | SFeq (_,v) ->
        begin match EcFol.sform_of_form v with
        | SFlocal _ -> true
        | _ -> false
        end
      | _ -> false
      end
    | _ -> false
    end
  in
  let try_rewriting_step (proof : EcCoreGoal.proof) : EcCoreGoal.proof option =
    let proof_a = try move_hash proof with _ -> proof in
    let count = count_hyp_forms proof p_id in
    let count_a = count_hyp_forms proof_a p_id in
    if (count <> count_a)
    then 
      Some proof_a
    else
      let left_first = go_left_first proof in
      try 
        if left_first
        then move_left_simplify proof
        else move_right_simplify proof
      with _ ->
        try 
          if left_first
          then move_right_simplify proof
          else move_left_simplify proof
       with _ -> None
  in
  progression try_rewriting_step proof
  
let move_down (h_id : EcIdent.t) (proof : EcCoreGoal.proof) 
: EcCoreGoal.proof =
  move_hyp_form_to_concl h_id proof
  


let rotate_hyps (proof : EcCoreGoal.proof) (p_id : EcIdent.t) 
: EcCoreGoal.proof =
  print_endline "BEGIN rotate_hyps";
  let proof_a = move_all_hyps_up proof p_id in
  let pregoal = get_only_pregoal proof_a in
  let h = (EcEnv.LDecl.tohyps pregoal.g_hyps).h_local in
  let form_ids = List.filter_map 
    (
      fun (n,l_k) -> 
        match (n,l_k) with 
        | (n, EcBaseLogic.LD_hyp _) -> Some n 
        | _ -> None 
    ) h 
  in
  match form_ids with
  | [] -> 
    proof
  | hd :: tl -> 
    let proof_b = List.fold_left (fun pr id -> move_down id pr) proof_a tl  in
    let proof_c = move_down hd proof_b in
    print_endline "END rotate_hyps";
    proof_c

let try_simplification_cycle (p_id : EcIdent.t) (proof : EcCoreGoal.proof) 
: EcCoreGoal.proof option =
  let rec try_simpcyc_r 
  (counter : int) (proof : EcCoreGoal.proof) 
  : EcCoreGoal.proof option 
  = if counter=0 then None
    else
      match try_rewriting proof p_id with
      | Some pr -> Some pr
      | None -> try_simpcyc_r (counter-1) (rotate_hyps proof p_id) 
  in
  let counter = count_hyp_forms proof p_id in
  try_simpcyc_r counter proof
  
let try_simp (proof : EcCoreGoal.proof) (p_id : EcIdent.t) 
: EcCoreGoal.proof option = 
  progression (try_simplification_cycle p_id) proof 

let simplify_heuristic (proof : EcCoreGoal.proof) (p_id : EcIdent.t) 
: EcCoreFol.form =
  (*let proof_a = prelims proof p_id in*)
  let proof' = move_all_hyp_forms_to_concl proof in
  let proof_o = try_simp proof' p_id in
  match proof_o with
  | None -> extract_form proof p_id
  | Some pr ->
    let pr' = move_all_hyps_up pr p_id in 
    extract_form pr' p_id

(*
let simplify_by_crushing 
(proof : EcCoreGoal.proof) 
(p_id : EcIdent.t) 
: EcCoreFol.form =
(*simplification by crushing*)
  let default = extract_form proof p_id in
  let proof_m = move_all_hyp_forms_to_concl proof in
  let proof_c = crush proof_m in
(*if conclusion is p(f), return f, otherwise return original formula*)
  let form_s =	
    let goal = EcCoreGoal.opened proof_c in
    begin match goal with
    | Some (1, pregoal) ->
      let c = pregoal.g_concl in
      begin match (EcCoreFol.f_node c) with
      | Fapp (f, [fs]) -> 
        begin match (EcCoreFol.f_node f) with
        | Flocal id when id = p_id -> fs
        | _ -> default
        end
      | _ -> default
      end
    | _ -> default
    end 
  in
  form_s
*)
              
let simplify_formula (hyps : EcEnv.LDecl.hyps) (form : EcCoreFol.form) 
: EcCoreFol.form =
(*for conclusion, make a dummy predicate p with form as input*)
  let f_ty = EcCoreFol.f_ty form in
  let p_ty = EcTypes.tcpred f_ty in
  let p_name = EcUid.NameGen.ofint (EcUid.unique ()) in
  let p_id = EcEnv.LDecl.fresh_id hyps p_name in
(*add predicate p to hypotheses*)
  let l_k = EcBaseLogic.LD_var (p_ty, None) in
  let hyps = EcEnv.LDecl.add_local p_id l_k hyps in
(*make concl and start proof*)  
  let fp = EcCoreFol.f_local p_id p_ty in
  let concl = EcCoreFol.f_app fp [form] EcTypes.tbool in
  let proof = EcCoreGoal.start hyps concl in
  pp_proof proof;
(*try to simplify form*)  
  (*simplify_by_crushing proof p_id*)
  simplify_heuristic proof p_id

let get_ty_from_oty (oty : EcTypes.ty) =  
  match oty.ty_node with
  | Tconstr (p,[ty]) when p = EcCoreLib.CI_Option.p_option -> ty
  | _ -> failwith "type is not an option type"


let ppe_ofhyps hyps = 
  let env = EcEnv.LDecl.toenv hyps in
  EcPrinting.PPEnv.ofenv env

let pp_ty hyps ty =
  let ppe = ppe_ofhyps hyps in
  Format.eprintf "%a@." (EcPrinting.pp_type ppe) ty
  
let pp_f hyps f =
  let ppe = ppe_ofhyps hyps in
  Format.eprintf "%a@." (EcPrinting.pp_form ppe) f
  
let printEvalResult (res : eval_condition_result) : unit =
  match res with
  | Bool true  -> print_endline "TRUE"
  | Bool false -> print_endline "FALSE"
  | Undecided  -> print_endline "UNDECIDED"

(*comment out for printf debugging*)
let pp_ty _ _ = ()
let pp_f _ _ = ()  
let printEvalResult _ = ()

(* adapted from EcHiGoal.ml process_delta *)
let rewrite_operator (opf : EcCoreFol.form) (tc:EcCoreGoal.tcenv1) =
  let path, _ = EcCoreFol.destr_op opf in
  let _, hyps, concl = EcCoreGoal.FApi.tc1_eflat tc in
  let check_op = fun p -> 
    if EcSymbols.sym_equal (EcPath.basename p) (EcPath.basename path) 
    then `Force 
    else `No 
  in
  let check_id = fun y -> 
    EcSymbols.sym_equal (EcIdent.name y) (EcPath.basename path) 
  in
  let ri =
    { EcReduction.no_red with
        EcReduction.delta_p = check_op;
        EcReduction.delta_h = check_id; } 
  in
  let redform = EcReduction.simplify ri hyps concl in
  EcLowGoal.t_change ~ri ?target:None redform tc
   
let eval_op_form_not_None 
(hyps : EcEnv.LDecl.hyps) 
(opf : EcCoreFol.form) 
(form : EcCoreFol.form)
(pi : EcProvers.prover_infos)
: bool =
  print_endline "smt_op_form_not_None";
  pp_f hyps opf;
  pp_f hyps form;
  let _,oty = EcTypes.tyfun_flat (EcCoreFol.f_ty opf) in
  pp_ty hyps oty;
  let ty = get_ty_from_oty oty in
  pp_ty hyps ty;
  let f_none = EcCoreFol.f_op EcCoreLib.CI_Option.p_none [ty] oty in
  (*EcTypes.toption ty*)
  pp_f hyps f_none;
  let concl = EcCoreFol.f_eq (EcCoreFol.f_app opf [form] oty) f_none in
  pp_f hyps concl;
  print_endline "let er = evalCondition hyps concl in";
  let rw_get_as_op = rewrite_operator opf in 
  let er = eval_condition_pre_tacs hyps concl pi [rw_get_as_op] in
  printEvalResult er;
  print_endline "match er with";
  match er with
  | Bool false -> true
  | _ -> false
  
let mk_oget_op_form
(opf : EcCoreFol.form) (form : EcCoreFol.form) : EcCoreFol.form =
  let _,oty = EcTypes.tyfun_flat (EcCoreFol.f_ty opf) in
  let ty = get_ty_from_oty oty in
  let as_ty_f = EcCoreFol.f_app opf [form] oty in
  let ogetf = 
  EcCoreFol.f_op EcCoreLib.CI_Option.p_oget [ty] 
  (EcTypes.tfun (EcTypes.toption ty) ty) in
  EcCoreFol.f_app ogetf [as_ty_f] ty

let deconstruct_data_simplify hyps form =
  let sf = simplify_formula hyps form in
  let opptyl, argforms = EcCoreFol.destr_op_app sf in
  let ctorsym = EcPath.basename (fst opptyl) in
  (ctorsym, argforms)
  

let deconstruct_data_eval_not_None p ty_args tyd ty_dtyo ty_dt hyps form pi =
  let sopl = 
    EcInductive.datatype_projectors (p, tyd.EcDecl.tyd_params, ty_dt) 
  in
  let sopfl = List.map (
    fun (s,op) ->
    let _, op_ret_ty = EcTypes.tyfun_flat op.EcDecl.op_ty in
    let opf = 
      EcCoreFol.f_op (EcInductive.datatype_proj_path p s) ty_args op_ret_ty
    in
    (s,opf)
  )       
  sopl in
  print_endline 
      "let opfo = List.find_opt (fun opf -> smt_op_form_not_None hyps opf form pi) 
      opfl in";
  let sopfo = List.find_opt 
  (fun (s,opf) -> eval_op_form_not_None hyps opf form pi)
  sopfl in
  print_endline "begin match opfo with";
  match sopfo with
  | Some (s, opf) ->
    let ogetf = simplify_formula hyps (mk_oget_op_form opf form) in
    let path = EcPath.pqoname (EcPath.prefix p) s in
    let env = EcEnv.LDecl.toenv hyps in
    let op = EcEnv.Op.by_path path env in
    let dom , _ = EcTypes.tyfun_flat op.EcDecl.op_ty in
    let args = 
      match (List.length dom) with
      | 0 -> []
      | 1 -> [ogetf]
      | _ -> 
        List.mapi (
          fun i argty -> let argf = EcCoreFol.f_proj ogetf i argty in
          simplify_formula hyps argf 
        ) dom
    in 
    (s , args)
  | None -> failwith "Couldn't find the operator for deconstruction"


let deconstruct_data 
(hyps : EcEnv.LDecl.hyps) 
(form : EcCoreFol.form) 
(pi : EcProvers.prover_infos)
: EcSymbols.symbol * (EcCoreFol.form list) =
  let ty = EcCoreFol.f_ty form in
  print_endline "begin match ty.ty_node with";
  begin match ty.ty_node with
  | Tconstr (p,ty_args) ->
    let env = EcEnv.LDecl.toenv hyps in
    let tyd = EcEnv.Ty.by_path p env in
    let ty_dtyo = EcDecl.tydecl_as_datatype tyd in
    print_endline "begin match ty_dtyo with";
    begin match ty_dtyo with
    | Some ty_dt ->
      begin try
        let ret = deconstruct_data_simplify hyps form in
        debugging_message (fun fmt -> Format.fprintf fmt 
        "deconstruction by simplification succeded.@.");
        ret
      with _ ->
        debugging_message (fun fmt -> Format.fprintf fmt 
        "deconstruction by simplification failed.@. 
         Trying to simplify by evaluating get_as_Constr@.");
      deconstruct_data_eval_not_None p ty_args tyd ty_dtyo ty_dt hyps form pi
      end
    | None -> failwith "Only data types can be deconstructed"
    end
  | _ -> failwith "Only constructed types can be deconstructed"
  end



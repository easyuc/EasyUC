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

  Format.printf "%a@."
    (EcPrinting.pp_goal (EcPrinting.PPEnv.ofenv (EcCoreGoal.FApi.tc_env tc)) 
    {prpo_pr = true; prpo_po = true})
    (hd, `All tl)

let pp_proof (proof : EcCoreGoal.proof) : unit =
  pp_tc (EcCoreGoal.tcenv_of_proof proof)

let ppe_ofhyps hyps = 
  let env = EcEnv.LDecl.toenv hyps in
  EcPrinting.PPEnv.ofenv env

let pp_ty hyps ty =
  let ppe = ppe_ofhyps hyps in
  Format.printf "%a@." (EcPrinting.pp_type ppe) ty
  
let pp_f hyps f =
  let ppe = ppe_ofhyps hyps in
  Format.printf "%a@." (EcPrinting.pp_form ppe) f

let pp_form tc1 f =
  let ppe = EcPrinting.PPEnv.ofenv (EcCoreGoal.FApi.tc1_env tc1) in
  Format.printf "%a@." (EcPrinting.pp_form ppe) f

let pp_form_ty tc1 f =
  let ppe = EcPrinting.PPEnv.ofenv (EcCoreGoal.FApi.tc1_env tc1) in
  Format.printf "%a@." (EcPrinting.pp_type ppe) (EcCoreFol.f_ty f)

let printEvalResult (res : eval_condition_result) : unit =
  match res with
  | Bool true  -> print_endline "TRUE"
  | Bool false -> print_endline "FALSE"
  | Undecided  -> print_endline "UNDECIDED"

(*comment out for printf debugging*)
let pp_ty _ _ = ()
let pp_f _ _ = ()
let pp_form _ _ = ()  
let pp_form_ty _ _ = ()
let printEvalResult _ = ()
let print_endline' = print_endline
let print_endline _ = ()
let pp_proof' = pp_proof
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

let get_last_pregoal (proof : EcCoreGoal.proof) : EcCoreGoal.pregoal =
  let goal = EcCoreGoal.opened proof in
  match goal with
  | Some (_, pregoal) -> pregoal
  | _ -> failwith "failed getting the last pregoal"
  
let move_all_hyp_forms_to_concl (proof : EcCoreGoal.proof) : EcCoreGoal.proof =
  let hyps = (get_last_pregoal proof).g_hyps  in
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
    Gc.compact ();
    print_endline (match b with true -> "SMT true" | false -> "SMT false");
    b
  with e when e <> Sys.Break ->
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

let unique_id_for_proof (proof : EcCoreGoal.proof) : EcIdent.t = 
  let pregoal = get_last_pregoal proof in
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

(*move => //=.*)
let move_simplify_trivial (proof : EcCoreGoal.proof) : EcCoreGoal.proof =
  let intro1_done tc = (*modified from ecHiGoal.ml*)
    EcCoreGoal.FApi.t_seq 
    (EcLowGoal.t_simplify ~delta:`No ~logic:(Some `Full))
    EcHiGoal.process_trivial
    tc
  in
  print_endline "move => //=.";
  run_tac intro1_done proof
  

let eq_proof_concl (proof1 : EcCoreGoal.proof) (proof2 : EcCoreGoal.proof)
: bool =
  if (EcCoreGoal.closed proof1)&&(EcCoreGoal.closed proof2)
  then true
  else
    (
      List.equal (EcCoreGoal.eq_handle)
      (EcCoreGoal.all_hd_opened proof1) (EcCoreGoal.all_hd_opened proof2)
    )
    &&
    (
      let pregoal1 = get_last_pregoal proof1 in
      let concl1 = pregoal1.g_concl in
      let pregoal2 = get_last_pregoal proof2 in
      let concl2 = pregoal2.g_concl in
      if EcCoreFol.f_equal concl1 concl2
      then true
      else false 
     )

let changed_proof (proof : EcCoreGoal.proof) (proof' : EcCoreGoal.proof)
: EcCoreGoal.proof option =
  if eq_proof_concl proof proof'
  then None
  else Some proof'
  
let try_move_simplify (proof : EcCoreGoal.proof) : EcCoreGoal.proof option =
  let proof' = move_simplify proof in
  changed_proof proof proof'

let try_move_simplify_trivial (proof : EcCoreGoal.proof) 
    : EcCoreGoal.proof option =
  let proof' = move_simplify_trivial proof in
  changed_proof proof proof'

(*
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
 *)

let extract_form (proof : EcCoreGoal.proof) (p_id : EcIdent.t) 
: EcCoreFol.form =
  let pregoal = get_last_pregoal proof in
  let concl = pregoal.g_concl in
  begin match (EcCoreFol.f_node concl) with
  | Fapp (f, [fs]) -> 
    begin match (EcCoreFol.f_node f) with
    | Flocal id when id = p_id -> fs
    | _ -> failwith "extract_form failed - not application of p_id"
    end
  | _ -> failwith "extract_form failed - not application"
  end

let rec move_all_hyps_up (proof : EcCoreGoal.proof) : EcCoreGoal.proof =
  try
    let proof' = move_up proof in
    move_all_hyps_up proof'
  with e when e <> Sys.Break -> proof

let should_simplify_further
      (proof : EcCoreGoal.proof) (p_id : EcIdent.t) : bool =
  print_endline "should_simplify_further?";
  let proof = move_all_hyps_up proof in
  let hyps = (get_last_pregoal proof).g_hyps  in
  let env = EcEnv.LDecl.toenv hyps in
  let concl = try extract_form proof p_id
              with e when e <> Sys.Break -> (get_last_pregoal proof).g_concl
  in
  pp_proof proof;
  let is_weakly_simplified (f : EcAst.form) : bool =
    let is_int_non_opp (f : EcAst.form) : bool =
      match f.EcAst.f_node with
      | Fint _ -> true
      | _      -> false
    in
    let rec is_weak_simp f =
      match f.EcAst.f_node with
      | Fint _       -> true
      | Fop (op, _)  ->
        EcPath.p_equal op EcCoreLib.CI_Unit.p_tt    ||
        EcPath.p_equal op EcCoreLib.CI_Bool.p_true  ||
        EcPath.p_equal op EcCoreLib.CI_Bool.p_false ||
        EcEnv.Op.is_dtype_ctor env op
      | Fapp (f, fs) ->
          (match f.f_node with
           | Fop (op, _) ->
               if EcEnv.Op.is_dtype_ctor env op
                 then List.for_all is_weak_simp fs
               else if EcFol.f_equal f EcFol.fop_int_opp  (* int negation *)
                 then (match fs with
                       | [g] -> is_int_non_opp g
                       | _   -> false)
               else false
           | _           -> false)
      | Ftuple fs    -> List.for_all is_weak_simp fs
      | _            -> false
    in is_weak_simp f
  in
  (*TODO add more conditions, like is_op?*)
  let ret = not (is_weakly_simplified concl) in
  print_endline ("should_simplify_further = "^(Bool.to_string ret));
  ret
                    
                                               

let progression 
(f : EcCoreGoal.proof -> EcCoreGoal.proof option)
(proof : EcCoreGoal.proof) : EcCoreGoal.proof option =
  print_endline "progression";
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

let process_rewrite_core ?(close = true) 
(rwi : EcHiGoal.LowRewrite.rwinfos)
(pt  : EcProofTerm.pt_ev)
(tc  : EcCoreGoal.tcenv1) =
  let tc = EcHiGoal.LowRewrite.t_rewrite_r rwi pt tc in
  let cl = fun tc ->
    if EcFol.f_equal EcFol.f_true (EcCoreGoal.FApi.tc1_goal tc) then
      EcLowGoal.t_true tc
    else EcLowGoal.t_id tc
  in 
  if close then EcCoreGoal.FApi.t_last cl tc else tc

(* adapted from ecHiGoal.ml process_delta *)
let process_delta_when_args_are_addr_literals p tc =
  print_endline "process_delta_when_args_are_addr_literals";
  let is_addr_literal (form : EcCoreFol.form) : bool =
    print_endline "is_addr_literal";
    pp_form tc form;
    let is_int_literal (form : EcCoreFol.form) : bool =
      print_endline "is_int_literal";
      pp_form tc form;
      let is =
      match form.f_node with
      | Fint _ -> true
      | _ -> false
      in
      print_endline (string_of_bool is);
      is
    in
    let is_list_cons (form : EcCoreFol.form) : bool =
      print_endline "is_list_cons";
      pp_form tc form;
      let lcp = EcPath.fromqsymbol (["Top"; "List"],"::") in
      let is =
      match form.f_node with
      | Fop (p, _) -> print_endline (EcPath.tostring p);
                      print_endline (EcPath.tostring lcp);
                      p = lcp
      | _ -> false
      in
      print_endline (string_of_bool is);
      is
    in
    let is_empty_list (form : EcCoreFol.form) : bool =
      print_endline "is_empty_list";
      pp_form tc form;
      let elp = EcPath.fromqsymbol (["Top"; "List"],"[]") in
      let is =
      match form.f_node with
      | Fop (p, _) when p = elp -> true
      | _ -> false
      in
      print_endline (string_of_bool is);
      is
    in
    let rec check (form : EcCoreFol.form) : bool =
      print_endline "check";
      pp_form tc form;
      (is_empty_list form)
      ||
      match form.f_node with   
      | Fapp (fop, fargs) ->
         if (List.length fargs) >= 2
         then
           (is_list_cons fop) &&
           (is_int_literal (List.hd fargs)) &&
           (check (List.hd (List.tl fargs)))
         else begin
           print_endline "wrong no of args for";
           pp_form tc fop;
           false end
      | _ ->
         print_endline "form not Fapp";
         false
                                                       
    in
    let islit = check form in
    print_endline (string_of_bool islit);
    islit
  in
  
  print_endline "tc1_eflat";
  let env, hyps, concl = EcCoreGoal.FApi.tc1_eflat tc in  
  print_endline "concl="; pp_form tc concl;
  (* Continue with matching based unfolding *)
  print_endline "tc1_process_pattern";
  let (ptenv, p) =
    let (ps, ue), p = EcProofTyping.tc1_process_pattern tc p in
    let ev = EcMatching.MEV.of_idents (EcIdent.Mid.keys ps) `Form in
      (EcProofTerm.ptenv (EcCoreGoal.(!!)tc) hyps (ue, ev), p)
  in
  print_endline "p="; pp_form tc p; pp_form_ty tc p;

  print_endline "(tvi, tparams, body, args, dp)";
  let (tvi, tparams, body, args, dp) =
    match EcFol.sform_of_form p with
    | EcFol.SFop (p, args) -> begin
        let op = EcEnv.Op.by_path (fst p) env in

        match op.EcDecl.op_kind with
        | EcDecl.OB_oper (Some (EcDecl.OP_Plain f)) ->
            (snd p, op.EcDecl.op_tparams, f, args, Some (fst p))
        | EcDecl.OB_pred (Some (EcDecl.PR_Plain f)) ->
            (snd p, op.EcDecl.op_tparams, f, args, Some (fst p))
        | _ ->
            print_endline "the operator cannot be unfolded";
            EcCoreGoal.tc_error (EcCoreGoal.(!!)tc) "the operator cannot be unfolded"
    end
    | _ ->
       print_endline "not headed by an operator/predicate";
       EcCoreGoal.tc_error (EcCoreGoal.(!!)tc) "not headed by an operator/predicate"

  in
  print_endline "full_red";
  let ri = { EcReduction.full_red with
               delta_p = (fun p -> if Some p = dp then `Force else `IfTransparent)} in
  let na = List.length args in

  begin
    print_endline "matches";
    let matches =
      try  ignore (EcProofTerm.pf_find_occurence ptenv ~ptn:p concl); true
      with EcProofTerm.FindOccFailure _ -> false
    in
    print_endline (string_of_bool matches);

    if matches then begin
      print_endline "concretize_form";
      let p    = EcProofTerm.concretize_form ptenv p in
      print_endline "p="; pp_form tc p; pp_form_ty tc p;
      let cpos =
        let test = fun _ fp ->
          let (fp : EcCoreFol.form) =
            match fp.EcAst.f_node with
            | EcAst.Fapp (h, hargs) when List.length hargs > na ->
                let (a1, a2) = BatList.takedrop na hargs in
                EcCoreFol.f_app h a1
                  (EcTypes.toarrow
                     (List.map EcCoreFol.f_ty a2) fp.EcAst.f_ty)
            | _ -> fp
          in
          print_endline "fp="; pp_form tc fp;  pp_form_ty tc fp;
          print_endline
            ("f_equal p fp = "^(string_of_bool (EcCoreFol.f_equal p fp)));
          begin
            let check_ty env subst ty1 ty2 =
              (*let ppe = EcPrinting.PPEnv.ofenv env in
              print_endline "check_ty ty1,ty2 = ";
              Format.printf "%a@." (EcPrinting.pp_type ppe) ty1;
              Format.printf "%a@." (EcPrinting.pp_type ppe) ty2;*)
  EcReduction.EqTest.for_type env ty1 (EcSubst.subst_ty subst ty2) in
            match p.EcAst.f_node, fp.EcAst.f_node with
            | Fop (pp,pp_ty), Fop(fpp,fpp_ty) ->
               let p_equal = EcPath.p_equal pp fpp in
           print_endline
           ("p_equal = "^(string_of_bool p_equal));
           if p_equal
           then List.iter2 ( fun ty1 ty2 ->
                  print_endline (string_of_bool (check_ty env EcSubst.empty ty1 ty2))) pp_ty fpp_ty
            else ()
        | _ -> () end;
          if EcReduction.is_alpha_eq hyps p fp
          then begin
              print_endline "is_alpha_eq YES";
              `Accept (-1)
            end
          else begin
              print_endline "is_alpha_eq NO";
              `Continue
              end
        in
          EcMatching.FPosition.select test concl
      in

      let target =
        EcMatching.FPosition.map cpos
          (fun topfp ->
            let (fp, args) = EcFol.destr_app topfp in
            
            match EcFol.sform_of_form fp with
            | EcFol.SFop ((_, tvi), []) ->
              if List.for_all is_addr_literal args
              then begin
                let body  =
                  EcFol.Tvar.f_subst ~freshen:true (List.map fst tparams)
                  tvi body in
                let body  = EcFol.f_app body args topfp.f_ty in
                try  EcReduction.h_red EcReduction.beta_red hyps body
                with EcEnv.NotReducible -> body
              end else
                topfp
           | _ -> assert false)
          concl
      in
        EcLowGoal.t_change ~ri ?target:None target tc
      end else begin
      print_endline "t_id";
      EcLowGoal.t_id tc
      end
  end


(* adapted from EcHiGoal.ml process_delta *)
let selective_rewrite_operator 
(opp : EcPath.path) 
(tc  : EcCoreGoal.tcenv1) =
  print_endline ("selective_rewrite_operator "^(EcPath.tostring opp));
  let pform_of_opp (opp : EcPath.path) : EcParsetree.pformula =
    let qs = EcPath.toqsymbol opp in
    let pqs = UcUtils.dummyloc qs in
    UcUtils.dummyloc (EcParsetree.PFident (pqs, None))
  in
  let p = pform_of_opp opp in
  process_delta_when_args_are_addr_literals p tc
  

let try_rewrite_addr_ops_on_literals (proof : EcCoreGoal.proof)
    : EcCoreGoal.proof option =
  print_endline "try_rewrite_addr_ops_on_literals";
  let addr_ops : EcPath.path list =
    let inc = EcPath.fromqsymbol (["UCListPO"],"inc") in
    let les = EcPath.fromqsymbol (["UCListPO"],"<") in
    let leq = EcPath.fromqsymbol (["UCListPO"],"<=") in
    [inc; les; leq]
  in
  let p' = List.fold_left (fun pr opp ->
    let tac = selective_rewrite_operator opp in
    try
      print_endline "run selective_rewrite_operator";
      run_tac tac pr
    with e when e <> Sys.Break ->
      print_endline
        ("selective_rewrite_operator EXCEPTION: "
         ^(Printexc.to_string e)^(Printexc.get_backtrace()));
      pr
                 ) proof addr_ops
  in
  changed_proof proof p'
  
let process_rewrite1_core ?(close = true) s pt tc =
  try
    process_rewrite_core ~close:close (s, None, None) pt tc
  with
  | EcHiGoal.LowRewrite.RewriteError e ->
     let tc_error s = EcCoreGoal.tc_error (EcCoreGoal.(!!)tc) s in
      match e with
      | EcHiGoal.LowRewrite.LRW_NotAnEquation ->
          tc_error "not an equation to rewrite"
      | EcHiGoal.LowRewrite.LRW_NothingToRewrite ->
          tc_error "nothing to rewrite"
      | EcHiGoal.LowRewrite.LRW_InvalidOccurence ->
          tc_error "invalid occurence selector"
      | EcHiGoal.LowRewrite.LRW_CannotInfer ->
          tc_error "cannot infer all placeholders"
      | EcHiGoal.LowRewrite.LRW_IdRewriting ->
          tc_error "refuse to perform an identity rewriting"
      | EcHiGoal.LowRewrite.LRW_RPatternNoMatch ->
          tc_error "r-pattern does not match the goal"
      | EcHiGoal.LowRewrite.LRW_RPatternNoRuleMatch ->
          tc_error "r-pattern does not match the rewriting rule"


let intro1_rw s tc = (*modified from ecHiGoal.ml*)
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

let count_hyp_forms (proof : EcCoreGoal.proof) : int =
  print_endline "BEGIN count_hyp_forms";
  let proof' = move_all_hyps_up proof in
  let pregoal = get_last_pregoal proof' in
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

(*
  let rw_tac tc = EcCoreGoal.FApi.t_ors (List.map do1 rw_lems) tc in
  let tac tc = EcCoreGoal.FApi.t_do `All None rw_tac tc in
  try
    pp_proof proof;
    let p' = run_tac tac proof in
    print_endline "***RW SUCCESS***";
    pp_proof p';
    changed_proof proof p'
  with e -> print_endline
("***RW EXCEPTION***"^(Printexc.to_string e)^(Printexc.get_backtrace()));
    None
 *)
let try_hyp_rewriting (proof : EcCoreGoal.proof) (p_id : EcIdent.t)
: EcCoreGoal.proof option =
  let move_right_simplify proof =
    let proof_a = move_right proof in
    let proof_b = move_simplify proof_a in
    Some proof_b
  in
  let should_move_right proof =
    let concl = (get_last_pregoal proof).g_concl in
    begin match EcFol.sform_of_form concl with
    | SFimp (h,_) ->
      begin match EcFol.sform_of_form h with
      | SFeq (v,_) ->
        begin match EcFol.sform_of_form v with
        | SFlocal _ -> true
        | _ -> false
        end
      | _ -> true
      end
    | _ -> true
    end
  in
  
(*  let move_left_simplify proof =
    let proof_a = move_left proof in
    let proof_b = move_simplify proof_a in
    Some proof_b
  in
  let go_left_first proof =
    let concl = (get_last_pregoal proof).g_concl in
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
 *)
  let try_rewriting_step (proof : EcCoreGoal.proof) : EcCoreGoal.proof option =
    (*  let rewriting_step (proof : EcCoreGoal.proof) : EcCoreGoal.proof option =*)
      let proof_a = try move_hash proof with e when e <> Sys.Break -> proof in
      let count = count_hyp_forms proof in
      let count_a = count_hyp_forms proof_a in
      if (count <> count_a)
      then 
        Some proof_a
      else
        if should_move_right proof
        then try move_right_simplify proof with e when e <> Sys.Break -> None
        else None
(* let left_first = go_left_first proof in
        try 
          if left_first
          then move_left_simplify proof
          else move_right_simplify proof
        with _ ->
          try 
            if left_first
            then move_right_simplify proof
            else move_left_simplify proof
         with _ -> None *)
       (*  let po = try_move_simplify_trivial proof in
         match po with
         | Some p -> po
         | None -> let po = try_rewriting_hints proof rw_lems in
                   match po with
                   | Some p -> po
                   | None -> try_rewrite_addr_ops_on_literals proof*)
(*    in
    if should_simplify_further proof p_id
    then rewriting_step proof
    else None  *)
  in
  progression try_rewriting_step proof
  
let move_down (h_id : EcIdent.t) (proof : EcCoreGoal.proof) 
: EcCoreGoal.proof =
  move_hyp_form_to_concl h_id proof
  
let rotate_hyps (proof : EcCoreGoal.proof) : EcCoreGoal.proof =
  print_endline "BEGIN rotate_hyps";
  let proof_a = move_all_hyps_up proof in
  let pregoal = get_last_pregoal proof_a in
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

let try_hyp_rewriting_cycle 
(p_id : EcIdent.t) (proof : EcCoreGoal.proof)  : EcCoreGoal.proof option =
  let rec try_hypcyc_r 
  (counter : int) (proof : EcCoreGoal.proof) 
  : EcCoreGoal.proof option 
  = if counter=0 
    then 
      try_hyp_rewriting proof p_id
    else
      match try_hyp_rewriting proof p_id with
      | Some pr -> Some pr
      | None -> try_hypcyc_r (counter-1) (rotate_hyps proof) 
  in
  print_endline "try_hyp_rewriting_cycle";
  let proof' = move_all_hyp_forms_to_concl proof in
  let counter = count_hyp_forms proof' in
  let proof_o = try_hypcyc_r counter proof in
  match proof_o with
  | Some p ->
     print_endline "try_hyp_rewriting_cycle SUCCESS";
     Some (move_all_hyps_up p)
  | None ->
     print_endline "try_hyp_rewriting_cycle FAIL";
     None
  
let rec try_simp (proof : EcCoreGoal.proof)
          (rw_lems : EcPath.path list) (p_id : EcIdent.t)
        : EcCoreGoal.proof option =
  let simps =
    [
      try_rewrite_addr_ops_on_literals;
      try_move_simplify_trivial;
      try_hyp_rewriting_cycle p_id;
      try_rewriting_hints p_id rw_lems;
    ]
  in
  let simp proof =
    List.fold_left (
      fun acc simpt ->
        if acc <> None
        then acc
        else
          if (should_simplify_further proof p_id)
          then simpt proof
          else None
      ) None simps
  in
  print_endline "try_simp";
  progression simp proof

and try_rewriting_hints  (p_id : EcIdent.t) (rw_lems : EcPath.path list)
(proof : EcCoreGoal.proof) : EcCoreGoal.proof option =
  print_endline "try_rewriting_hints";
  let pregoal = get_last_pregoal proof in
  let penv = EcCoreGoal.proofenv_of_proof proof in
  let ptenv = EcProofTerm.ptenv_of_penv pregoal.g_hyps penv in
  let do1 lemma tc =
    print_endline ("process_rewrite1_core for "^(EcPath.tostring lemma));
    let pt = EcProofTerm.pt_of_uglobal_r (EcProofTerm.copy ptenv) lemma in
    process_rewrite1_core `LtoR pt tc
  in
  let goal_no proof = List.length (EcCoreGoal.all_opened proof) in
  let gn = goal_no proof in
  let try_rewriting_hint lemma =
    try
      let p' = run_tac (do1 lemma) proof in
      print_endline "***RW SUCCESS***";
      pp_proof p';
      if gn=1 && (goal_no p')>1
      then begin
        print_endline "goal no increased from one to more than one";
        match try_simp p' rw_lems p_id with
        | Some p'' ->
          if (goal_no p'') = 1
          then begin
              print_endline "goal no reduced back to one";
              changed_proof proof p''
            end else begin
              print_endline "failed to reduce goal no to one"; None end
        | None -> None
      end else changed_proof proof p'
    with e when e <> Sys.Break -> print_endline
("***RW EXCEPTION***"^(Printexc.to_string e)^(Printexc.get_backtrace()));
              None
  in
  pp_proof proof;
  List.fold_left (fun acc lem ->
      if acc<>None then acc else try_rewriting_hint lem) None rw_lems


let simplify_heuristic (proof : EcCoreGoal.proof) (p_id : EcIdent.t) 
(rw_lems : EcPath.path list) : EcCoreFol.form =
  (*let proof_a = prelims proof p_id in*)
  let proof_o = try_simp proof rw_lems p_id in
  match proof_o with
  | None -> extract_form proof p_id (* no progress happened *)
  | Some pr ->
    match List.length (EcCoreGoal.all_opened pr) with
    | 1 -> extract_form pr p_id         (* success - some progress happened *)
    | _ -> extract_form proof p_id  (* opened more goals than could be closed *)

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
    (rw_lems : EcPath.path list)  (* TODO - use repeatedly left-to-right *)
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
  print_endline "simplify_formula";
  pp_proof proof;
(*try to simplify form*)  
  (*simplify_by_crushing proof p_id*)
  simplify_heuristic proof p_id rw_lems

let eval_condition (hyps : EcEnv.LDecl.hyps) (form : EcCoreFol.form)
    (pi : EcProvers.prover_infos) (rw_lems : EcPath.path list)
      : eval_condition_result =
  let form = simplify_formula hyps form rw_lems in
  let () =
    debugging_message
    (fun fmt ->
       Format.fprintf fmt
       "@[@[formula@ simplified@ to:@]@\n@[%a@]@]"
       (EcPrinting.pp_form (ppe_ofhyps hyps)) form) in
  if EcFol.is_true form
    then Bool true
  else if EcFol.is_false form
    then Bool false
  else eval_condition_pre_tacs hyps form pi []

let get_ty_from_oty (oty : EcTypes.ty) =  
  match oty.ty_node with
  | Tconstr (p,[ty]) when p = EcCoreLib.CI_Option.p_option -> ty
  | _ -> failwith "type is not an option type"

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

let deconstruct_data_simplify hyps form rw_lems =
  let env = EcEnv.LDecl.toenv hyps in
  let sf = simplify_formula hyps form rw_lems in
  let opptyl, argforms = EcCoreFol.destr_op_app sf in
  let opp = fst opptyl in
  if EcEnv.Op.is_dtype_ctor env opp
  then ((EcPath.basename opp), argforms)
  else failwith "Simplification did not reduce formula to the form of ctor applied to data."
  

let deconstruct_data_eval_not_None p ty_args tyd ty_dtyo ty_dt
    hyps form pi rw_lems =
  let sopl = 
    EcInductive.datatype_projectors (p, tyd.EcDecl.tyd_params, ty_dt) 
  in
  let sopfl = List.map (
    fun (s,op) ->
    let _, op_ret_ty = EcTypes.tyfun_flat op.EcDecl.op_ty in
    let opty =
      EcCoreSubst.Tvar.subst
      (EcCoreSubst.Tvar.init (List.map fst op.op_tparams) ty_args) op_ret_ty in
    let opf = 
      EcCoreFol.f_op (EcInductive.datatype_proj_path p s) ty_args opty
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
    let ogetf = simplify_formula hyps (mk_oget_op_form opf form) rw_lems in
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
          simplify_formula hyps argf rw_lems
        ) dom
    in 
    (s , args)
  | None -> failwith "Couldn't find the operator for deconstruction"


let deconstruct_data 
(hyps : EcEnv.LDecl.hyps) 
(form : EcCoreFol.form) 
(pi : EcProvers.prover_infos)
(rw_lems : EcPath.path list)  (* TODO - use repeatedly left-to-right *)
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
        let ret = deconstruct_data_simplify hyps form rw_lems in
        (*debugging_message (fun fmt -> Format.fprintf fmt 
        "deconstruction by simplification succeded.@.");*)
        ret
      with e when e <> Sys.Break ->
        (*debugging_message (fun fmt -> Format.fprintf fmt 
        "deconstruction by simplification failed.@. 
         Trying to simplify by evaluating get_as_Constr@.");*)
      deconstruct_data_eval_not_None p ty_args tyd ty_dtyo ty_dt
      hyps form pi rw_lems
      end
    | None -> failwith "Only data types can be deconstructed"
    end
  | _ -> failwith "Only constructed types can be deconstructed"
  end



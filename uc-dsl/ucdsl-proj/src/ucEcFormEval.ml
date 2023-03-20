open EcParsetree
open UcGenEcInterface

type evalConditionResult = 
  | Bool of bool
  | Undecided
  
(* ttenv constructed from current scope, maybe replace with concrete values, without accessing scope? *)
let get_ttenv () =
  let scope = EcCommands.ucdsl_current () in
  let scope = EcScope.Prover.process scope EcParsetree.empty_pprover in
  {
    EcHiGoal.tt_provers    = (fun _ -> {
      EcProvers.dft_prover_infos with pr_provers = EcProvers.dft_prover_names
      });
    EcHiGoal.tt_smtmode    = `Standard;
    EcHiGoal.tt_implicits  = true;
    EcHiGoal.tt_oldip      = false;
    EcHiGoal.tt_redlogic   = true;
  }

(*move => |>.*)
let ptac_crush : EcParsetree.ptactic = 
  {
    pt_core = dl (Plogic (Pmove {pr_rev = {pr_clear = []; pr_genp = []}; pr_view = []}));
    pt_intros = [`Ip [dl (IPCrush {cm_simplify = false; cm_solve = false})]]
  }

let run_tactic (ptac : EcParsetree.ptactic) (proof : EcCoreGoal.proof) : EcCoreGoal.proof =
  let ttenv = get_ttenv () in
  snd (EcHiTacticals.process ttenv [ptac] proof)

let crush (proof : EcCoreGoal.proof) : EcCoreGoal.proof =
  run_tactic ptac_crush proof

let ptac_move_hyp_forms_to_concl (hyp_names : string list) : EcParsetree.ptactic =
  let pr_genp = List.map (fun h -> `Form (None, pform_ident h) ) hyp_names in
  {
    pt_core = dl (Plogic (Pmove 
      {
        pr_rev = {pr_clear = []; pr_genp = pr_genp}; pr_view = []
      }));
    pt_intros = []
  }
  
let move_all_hyp_forms_to_concl (proof : EcCoreGoal.proof) : EcCoreGoal.proof =
  let hyps = 
    match EcCoreGoal.opened proof with
    | Some (1,pregoal) -> EcEnv.LDecl.tohyps pregoal.g_hyps
    | _ -> failwith "Hmmm...."
  in
  let hyp_names = List.filter_map ( fun h -> 
      match h with 
      | (id, EcBaseLogic.LD_hyp _) -> Some (EcIdent.name id) 
      | _ -> None
    ) hyps.h_local
  in
  let ptac = ptac_move_hyp_forms_to_concl hyp_names in
  run_tactic ptac proof

let pp_tc tc = (* copied from ecLowGoal.ml *)
  let pr = EcCoreGoal.proofenv_of_proof (EcCoreGoal.proof_of_tcenv tc) in
  let cl = List.map (fun h -> EcCoreGoal.FApi.get_pregoal_by_id h pr) (EcCoreGoal.FApi.tc_opened tc) in
  let cl = List.map (fun (x:EcCoreGoal.pregoal) -> (EcEnv.LDecl.tohyps x.g_hyps, x.g_concl)) cl in

  match cl with [] -> () | hd :: tl ->

  Format.eprintf "%a@."
    (EcPrinting.pp_goal (EcPrinting.PPEnv.ofenv (EcCoreGoal.FApi.tc_env tc)) {prpo_pr = true; prpo_po = true})
    (hd, `All tl)

let pp_proof (proof : EcCoreGoal.proof) : unit =
  pp_tc (EcCoreGoal.tcenv_of_proof proof)

let can_prove_smt (proof : EcCoreGoal.proof) : bool =
  let dft_pi = { 
    EcProvers.dft_prover_infos with pr_provers = EcProvers.dft_prover_names
  } in
  let goal = EcCoreGoal.opened proof in
  try
    match goal with
    | Some (1, pregoal) -> EcSmt.check dft_pi pregoal.g_hyps pregoal.g_concl
    | _ -> false
  with _ -> false

let can_prove_crush (proof : EcCoreGoal.proof) : bool =
  let proof_m = move_all_hyp_forms_to_concl proof in
  let proof_c = crush proof_m in
  EcCoreGoal.closed proof_c

let can_prove (proof : EcCoreGoal.proof) : bool =
  if can_prove_crush proof
    then true
    else can_prove_smt proof

let to_LDecl_hyps (hyps : EcBaseLogic.hyps) : EcEnv.LDecl.hyps =
  let local_h = List.rev hyps.h_local in
  let env = UcEcInterface.env () in
  EcEnv.LDecl.init env ~locals:local_h hyps.h_tvar

let evalCondition (hyps : EcBaseLogic.hyps) (form : EcCoreFol.form) : evalConditionResult =
  let hyps = to_LDecl_hyps hyps in
  let proof_true = EcCoreGoal.start hyps form in
  let proof_false = EcCoreGoal.start hyps (EcCoreFol.f_not form) in

  if can_prove proof_true
    then
      Bool true
    else
      if can_prove proof_false
        then
          Bool false
        else
          Undecided
          
let rec unique_name (env : EcEnv.env) (hyps : EcBaseLogic.hyps) : string =
  let check_exists_in_env (n : string) : bool =
    false (*TODO do we need check?*)
  in
  let check_exists_in_hyps (n : string) : bool =
    let hypn = List.map (fun (id,_) -> EcIdent.name id) hyps.h_local in
    List.exists (fun hn -> hn = n) hypn
  in
 let check_exists (n : string) : bool =
    (check_exists_in_env n) || (check_exists_in_hyps n)   in
 let name = EcUid.NameGen.ofint (EcUid.unique ()) in
 if (check_exists name)
   then unique_name env hyps
   else name

let get_only_pregoal (proof : EcCoreGoal.proof) : EcCoreGoal.pregoal =
  let goal = EcCoreGoal.opened proof in
  match goal with
  | Some (1, pregoal) -> pregoal
  | _ -> failwith "failed getting the one and only pregoal"
      
let unique_name_for_proof (proof : EcCoreGoal.proof) : string = 
  let pregoal = get_only_pregoal proof in
  let hyps = EcEnv.LDecl.tohyps pregoal.g_hyps in
  let env = EcEnv.LDecl.toenv pregoal.g_hyps in
  unique_name env hyps    

(*move => [#].*)         
let ptac_move_hash : EcParsetree.ptactic =
  {
    pt_core = dl (Plogic (Pmove {pr_rev = {pr_clear = []; pr_genp = []}; pr_view = []}));
    pt_intros = [`Ip [dl (IPCase (`Full ((false, false), false, None), []))]]
  }

let move_hash (proof : EcCoreGoal.proof) : EcCoreGoal.proof =
  run_tactic ptac_move_hash proof

(*move => h_name.*)    
let ptac_move_up (h_name : string) : EcParsetree.ptactic =
  {
    pt_core = dl (Plogic (Pmove {pr_rev = {pr_clear = []; pr_genp = []}; pr_view = []}));
    pt_intros = [`Ip [ dl (IPCore (`Named h_name))]]
  }

let move_up (proof : EcCoreGoal.proof) : EcCoreGoal.proof =
  let h_name = unique_name_for_proof proof in
  let proof' = run_tactic (ptac_move_up h_name) proof in
  proof'

(*move => /=.*)
let ptac_move_simplify : EcParsetree.ptactic =
  {
    pt_core = dl (Plogic (Pmove {pr_rev = {pr_clear = []; pr_genp = []}; pr_view = []}));
    pt_intros = [`Ip [ dl (IPSimplify `Default)]]
  }

let move_simplify (proof : EcCoreGoal.proof) : EcCoreGoal.proof =
  run_tactic ptac_move_simplify proof

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
  
let extract_form (proof : EcCoreGoal.proof) (p_id : EcIdent.t) : EcCoreFol.form =
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
  
let move_hash_all (proof : EcCoreGoal.proof) (p_id : EcIdent.t) : EcCoreGoal.proof =
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

(*move => ->.*)  
let ptac_move_right : EcParsetree.ptactic =
  {
    pt_core = dl (Plogic (Pmove {pr_rev = {pr_clear = []; pr_genp = []}; pr_view = []}));
    pt_intros = [`Ip [ dl (IPRw (None, `LtoR, None))]]
  }

let move_right (proof : EcCoreGoal.proof) : EcCoreGoal.proof =
  run_tactic ptac_move_right proof

(*move => <-.*)
let ptac_move_left : EcParsetree.ptactic =
  {
    pt_core = dl (Plogic (Pmove {pr_rev = {pr_clear = []; pr_genp = []}; pr_view = []}));
    pt_intros = [`Ip [ dl (IPRw (None, `RtoL, None))]]
  }

let move_left (proof : EcCoreGoal.proof) : EcCoreGoal.proof =
  run_tactic ptac_move_left proof
  
let try_move_lr_all (proof : EcCoreGoal.proof) : EcCoreGoal.proof option =
  let try_move_lr_step (proof : EcCoreGoal.proof) : EcCoreGoal.proof option =
    try 
      let proof_a = move_right proof in
      let proof_b = move_simplify proof_a in
      Some proof_b
    with _ ->
      try 
        let proof_a = move_left proof in
        let proof_b = move_simplify proof_a in
        Some proof_b
      with _ -> None
  in
  progression try_move_lr_step proof 
  
let ptac_move_down (h_name : string) : EcParsetree.ptactic =
  ptac_move_hyp_forms_to_concl [h_name]
  
let move_down (h_id : EcIdent.t) (proof : EcCoreGoal.proof) : EcCoreGoal.proof =
  run_tactic (ptac_move_down (EcIdent.name h_id)) proof
  
let rec move_all_hyps_up (proof : EcCoreGoal.proof) (p_id : EcIdent.t) : EcCoreGoal.proof =
  if (is_concl_p proof p_id)
  then 
    proof
  else 
    let proof' = move_up proof in
    move_all_hyps_up proof' p_id

let count_hyp_forms (proof : EcCoreGoal.proof) (p_id : EcIdent.t) : int =
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
  List.length h_forms

let rotate_hyps (proof : EcCoreGoal.proof) (p_id : EcIdent.t) : EcCoreGoal.proof =
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
    let proof_b = move_down hd proof_a in
    let proof_c = List.fold_right (fun id pr -> move_down id pr) tl proof_b
    in 
    proof_c

let try_simplification_cycle (p_id : EcIdent.t) (proof : EcCoreGoal.proof) : EcCoreGoal.proof option =
  let rec try_simpcyc_r 
  (counter : int) (proof : EcCoreGoal.proof) 
  : EcCoreGoal.proof option 
  = if counter=0 then None
    else
      match try_move_lr_all proof with
      | Some pr -> Some pr
      | None -> try_simpcyc_r (counter-1) (rotate_hyps proof p_id) 
  in
  let counter = count_hyp_forms proof p_id in
  try_simpcyc_r counter proof
  
let try_simp (proof : EcCoreGoal.proof) (p_id : EcIdent.t) : EcCoreGoal.proof option = 
  progression (try_simplification_cycle p_id) proof 

let simplify_heuristic (proof : EcCoreGoal.proof) (p_id : EcIdent.t) : EcCoreFol.form =
  let proof_a = prelims proof p_id in
  let proof_o = try_simp proof_a p_id in
  match proof_o with
  | None -> extract_form proof p_id
  | Some pr -> extract_form pr p_id

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
              
let simplifyFormula (hyps : EcBaseLogic.hyps) (form : EcCoreFol.form) : EcCoreFol.form =
(*for conclusion, make a dummy predicate p with form as input*)
  let f_ty = EcCoreFol.f_ty form in
  let p_ty = EcTypes.tcpred f_ty in
  let p_name = EcUid.NameGen.ofint (EcUid.unique ()) in
  let p_id = EcIdent.create p_name in
(*add predicate p to hypotheses*)
  let l_k = EcBaseLogic.LD_var (p_ty, None) in
  let hyps = {hyps with h_local = hyps.h_local @ [(p_id,l_k)]} in
  let hyps = to_LDecl_hyps hyps in
(*make concl and start proof*)  
  let fp = EcCoreFol.f_local p_id p_ty in
  let concl = EcCoreFol.f_app fp [form] EcTypes.tbool in
  let proof = EcCoreGoal.start hyps concl in
(*try to simplify form*)  
  (*simplify_by_crushing proof p_id*)
  simplify_heuristic proof p_id








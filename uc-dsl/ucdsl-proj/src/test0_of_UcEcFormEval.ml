open EcParsetree

(*open UcGenEcInterface
let crush () : unit =
  let ptac = 
  {
    pt_core = dl (Plogic (Pmove {pr_rev = {pr_clear = []; pr_genp = []}; pr_view = []}));
    pt_intros = [`Ip [dl (IPCrush {cm_simplify = false; cm_solve = false})]]
  } in
  UcEcInterface.process (Gtactics (`Actual [ptac]))

let empty_ppr = {
                  pprov_max = None; 
                  pprov_timeout = None;
                  pprov_cpufactor = None; 
                  pprov_names = None;
                  pprov_quorum = None; 
                  pprov_verbose = None;
                  pprov_version = None; 
                  plem_all = None; 
                  plem_max = None;
                  plem_iterate = None; 
                  plem_wanted = None;
                  plem_unwanted = None; 
                  plem_selected = None;
                  psmt_debug = None
                }
let dft_pi = EcProvers.dft_prover_infos

let dft_ppr = 
  {
    pprov_max = Some dft_pi.pr_max; 
    pprov_timeout = Some dft_pi.pr_timelimit;
    pprov_cpufactor = Some dft_pi.pr_cpufactor; 
    pprov_names = Some 
    {
      pp_use_only = dll dft_pi.pr_provers;
      pp_add_rm   = [];
    };
    pprov_quorum = Some dft_pi.pr_quorum; 
    pprov_verbose = None;
    pprov_version = None; 
    plem_all = Some dft_pi.pr_all; 
    plem_max = None;
    plem_iterate = Some dft_pi.pr_iterate; 
    plem_wanted = None;
    plem_unwanted = None; 
    plem_selected = Some dft_pi.pr_selected;
    psmt_debug = Some dft_pi.gn_debug
  }

let smt () : unit =
  let ptac_smt : EcParsetree.ptactic =
    {
      pt_core = dl (Plogic (Psmt dft_ppr));
      pt_intros = []
    }
  in
  UcEcInterface.process (Gtactics (`Actual [ptac_smt]))
  
let pf_eq = pform_ident sym_eq

let sym_le = "<="

let pf_le = pform_ident sym_le

let pf_impl = pform_ident "=>"
  
let lemma_one_is_one () : unit =
  let one = pf_of_int 1 in
  let pfrm = pform_app pf_eq [one;one] in
  let plemma = paxiom_lemma "l_one_is_one" pfrm in
  decl_axiom plemma

let lemma_i_eq_one_impl_i_le_one () : unit =
  let one = pf_of_int 1 in
  let i = pform_ident "i" in
  let pfrm_i_eq_1 = pform_app pf_eq [i;one] in
  let pfrm_i_le_1 = pform_app pf_le [i;one] in
  let pfrm_lemma = pform_app pf_impl [pfrm_i_eq_1;pfrm_i_le_1] in
  let plemma = paxiom_lemma_vars "l_i_is_one" [("i",int_pty)] pfrm_lemma in
  decl_axiom plemma

let lemma_true () : unit =
  let pfrm = pform_ident "true" in
  let plemma = paxiom_lemma "l_true" pfrm in
  decl_axiom plemma*)
  
(* the substitution system has been changed in EasyCrypt, now using
   the f_subst mechanism for everything

   but I'm (Alley) not sure what you are trying to accomplish here... *)

let trans_prop (env : EcEnv.env) (ue : EcUnify.unienv) (pfrm : EcParsetree.pformula) : EcFol.form =
  let frm = EcTyping.trans_prop env ue pfrm in
  if not (EcUnify.UniEnv.closed ue)
    then failwith "the formula contains free type variables"
    else (*EcFol.Fsubst.uni (EcUnify.UniEnv.close ue)*) frm

(*
    let sty = { ty_subst_id with ts_u = subs } in
    let fs = EcFol.Fsubst.f_subst_init ~sty:sty () in
    EcFol.Fsubst.f_subst fs tform in
*)


 (*
let lemma_i_eq_one_impl_i_le_one' () : unit =
  let i_ = "i" in
  
  let i_id = EcIdent.create i_ in
  let i_ty = EcTypes.tint in

  let one = pf_of_int 1 in
  let i = pform_ident i_ in
  let pfrm_i_eq_1 = pform_app pf_eq [i;one] in

  let pfrm_i_le_1 = pform_app pf_le [i;one] in

  let env = UcEcInterface.env () in
  let env = EcEnv.Var.bind_local i_id i_ty env in
  let ue  = EcTyping.transtyvars env (EcLocation._dummy, None) in
  let hyp_i = trans_prop env ue pfrm_i_eq_1 in
 
  let concl = trans_prop env ue pfrm_i_le_1 in

  lemma_true ();
  
  let env = UcEcInterface.env () in
  let locals =
    [
     (EcIdent.create "i_eq_1" , EcBaseLogic.LD_hyp hyp_i);
     (i_id , EcBaseLogic.LD_var (i_ty, None))
    ]
    in
  let hyps = EcEnv.LDecl.init ~locals env [] in
  let proof = EcScope.PSCheck (EcCoreGoal.start hyps concl) in

  let scope = EcCommands.ucdsl_current () in  
  let puc = 
    match scope.sc_pr_uc with
    | Some puc -> puc
    | None -> failwith "Nooo..."
    in
  let puca =
    match puc.puc_active with
    | Some (puca, _) -> puca
    | None -> failwith "Noooo..."
    in
  let puca = {puca with puc_jdg = proof} in
  let puc = {puc with puc_active = Some (puca,None); puc_init = scope.sc_env} in
  let scope = {scope with sc_pr_uc = Some puc} in
  EcCommands.ucdsl_update scope
*)
let printEvalResult (res : UcEcFormEval.eval_condition_result) : unit =
  match res with
  | Bool true  -> print_endline "TRUE"
  | Bool false -> print_endline "FALSE"
  | Undecided  -> print_endline "UNDECIDED"
  
let printFormula env (form : EcCoreFol.form) : unit =
  Format.eprintf "%a@."
    (EcPrinting.pp_form (EcPrinting.PPEnv.ofenv env)) 
    (form)

let dl = UcUtils.dummyloc

let pf_of_int (i : int) : EcParsetree.pformula = 
  dl (PFint (EcBigInt.of_int i))
  
let pform_app (f : EcParsetree.pformula) (args : EcParsetree.pformula list) : EcParsetree.pformula =
  dl (PFapp (f,args))
  
let qs = EcParsetree.qsymb_of_symb

let pqs (name : string) = dl (qs name)
  
let pform_pqident (pqname : EcParsetree.pqsymbol) : EcParsetree.pformula =
  dl (PFident (pqname, None))
  
let pform_ident (name : string) : EcParsetree.pformula =
  pform_pqident (pqs name)

let sym_eq = "="

let pf_eq = pform_ident sym_eq

let to_LDecl_hyps (hyps : EcBaseLogic.hyps) : EcEnv.LDecl.hyps =
  let local_h = List.rev hyps.h_local in
  let env = UcEcInterface.env () in
  EcEnv.LDecl.init env ~locals:local_h hyps.h_tvar

let dft_pi = { 
    EcProvers.dft_prover_infos with 
      pr_provers = 
      List.filter EcProvers.is_prover_known EcProvers.dft_prover_names
  }

let testFormEval () : unit =
  let i_ = "i" in
  
  let i_id = EcIdent.create i_ in
  let i_ty = EcTypes.tint in

  let one = pf_of_int 1 in
  let zero = pf_of_int 0 in
  let i = pform_ident i_ in
  let pform_i_eq_1 = pform_app pf_eq [i;one] in

  let pform_i_eq_0 = pform_app pf_eq [i;zero] in

  let env = UcEcInterface.env () in
  let env = EcEnv.Var.bind_local i_id i_ty env in
  let ue  = EcTyping.transtyvars env (EcLocation._dummy, None) in

  let form_i_eq_1 = trans_prop env ue pform_i_eq_1 in
  let form_i_eq_0 = trans_prop env ue pform_i_eq_0 in
  
  let hyps_empty : EcEnv.LDecl.hyps = 
    to_LDecl_hyps
    {
      h_tvar = [];
      h_local = [(i_id, LD_var (i_ty,None))]
    } in
  
  let hyps_i_eq_0 : EcEnv.LDecl.hyps = 
    to_LDecl_hyps
    {
      h_tvar = [];
      h_local =
        [
          (i_id, LD_var (i_ty,None));
          (EcIdent.create "i_eq_0",LD_hyp form_i_eq_0)
        ]
    } in
  
  let hyps_i_eq_1 : EcEnv.LDecl.hyps = 
    to_LDecl_hyps
    {
      h_tvar = [];
      h_local = 
        [
          (i_id, LD_var (i_ty,None));
          (EcIdent.create "i_eq_1",LD_hyp form_i_eq_1)
        ]     
    } in
    
  printEvalResult (UcEcFormEval.eval_condition hyps_empty form_i_eq_0 dft_pi);
  printEvalResult (UcEcFormEval.eval_condition hyps_i_eq_0 form_i_eq_0 dft_pi);
  printEvalResult (UcEcFormEval.eval_condition hyps_i_eq_1 form_i_eq_0 dft_pi);
  
  printFormula env (UcEcFormEval.simplify_formula hyps_empty form_i_eq_0);
  printFormula env (UcEcFormEval.simplify_formula hyps_i_eq_0 form_i_eq_0);
  printFormula env (UcEcFormEval.simplify_formula hyps_i_eq_1 form_i_eq_0)
  

let () : unit =
  UcEcInterface.init ();
(*
  lemma_one_is_one ();
  proof ();
  smt ();
  qed ();*)

  UcEcInterface.require (dl "AllCore") (Some `Import);
  
(*  lemma_i_eq_one_impl_i_le_one ();
  proof ();
  crush(); 
  smt ();
  qed ();*)
(*  
  lemma_i_eq_one_impl_i_le_one' ();
  proof ();
  smt ();
  qed ();
*)

  testFormEval ()
  
  


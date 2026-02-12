(* UcPreamblePP module *)

(* Pretty Printing of UC Spec Preambles *)

open Format

open EcUtils
open EcSymbols
open EcLocation
open EcParsetree
open EcPrinting

open UcMessage

(* many of these functions will be partially applied - all but the
   final formatter argument - during typechecking, and only after the
   declaration or cloning in question was already checked by EasyCrypt
   (but the supplied environment will be the one in which the checking
   is done); consequently, they should never raise exceptions

   when using them with fprint, use %t (not %a) *)

type ppna = formatter -> unit  (* pp with no argument *)

let ppna_list_sep sep (ppnas : ppna list) : ppna =
  fun ppf ->
  let rec f (ppnas : ppna list) (ppf : formatter) =
    match ppnas with
    | []            -> ()
    | [ppna]        -> ppna ppf
    | ppna :: ppnas ->
        fprintf ppf "%t%(%)%t" ppna sep (f ppnas) in
  fprintf ppf "@[%t@]" (f ppnas)

let pp_abstract_type_decl (ptyd : ptydecl) : ppna =
  fun (ppf : formatter) ->
    let name = unloc ptyd.pty_name in
    let tyvars = List.map (unloc) ptyd.pty_tyvars in
    match List.length tyvars with
    | 0 -> fprintf ppf "@[type@ %s.@]" name
    | 1 -> fprintf ppf "@[type@ %s@ %s.@]" (List.hd tyvars) name
    | _ ->
        fprintf ppf "@[type@ (%a)@ %s.@]"
        (pp_list ",@ " pp_symbol) tyvars name

let pp_abstract_op_decl (env : EcEnv.env) (po : poperator) : ppna =
  fun (ppf : formatter) ->
    let ue = EcUnify.UniEnv.create None in
    let ppe = PPEnv.ofenv env in
    let tags = List.map unloc po.po_tags in
    let name = unloc (po.po_name) in
    let pty =
      match po.po_def with
      | PO_abstr pty -> pty
      | _            -> failure "cannot happen" in
    let ty = EcTyping.transty EcTyping.tp_tydecl env ue pty in
    let pp_tags ppf =
      fprintf ppf "@[[%a]@]" (pp_list "@ " pp_symbol) in
    match List.length tags with
    | 0 ->
        fprintf ppf "@[op@ %a@ :@ %a.@]"
        (pp_opname ppe) (EcPath.fromqsymbol (qsymb_of_symb name))
        (pp_type ppe) ty
    | _ ->
        fprintf ppf "@[op@ %a@ %a@ :@ %a.@]"
        pp_tags tags
        (pp_opname ppe) (EcPath.fromqsymbol (qsymb_of_symb name))
        (pp_type ppe) ty

let pgtybinding_to_ptybinding ((osyms, pgty) : pgtybinding)
      : ptybinding =
  (osyms,
   match pgty with
   | PGTY_Type pty -> pty
   | _             -> failure "cannot happen")

type aptybinding = symbol option list * EcAst.ty

let aptybindings_type_map (f : EcAst.ty -> EcAst.ty)
    (aptybs : aptybinding list) : aptybinding list =
  List.map (fun (osyms, ty) -> (osyms, f ty)) aptybs

let abs_ptybindings (env : EcEnv.env) (ue : EcUnify.unienv)
    (ptybs : ptybindings) : aptybinding list =
  List.map
  (fun (osyms, pty) ->
     (List.map (omap unloc) (List.map unloc osyms),
      EcTyping.transty EcTyping.tp_relax env ue pty))
  ptybs

let pp_aptybinding (ppe : PPEnv.t) (ppf : formatter)
    ((osyms, ty) : aptybinding) : unit =
  let pp_osym (ppf : formatter) (osym : symbol option) =
    match osym with
    | None   -> fprintf ppf "_"
    | Some s -> fprintf ppf "%s" s in
  fprintf ppf "@[(@[%a@ :@ %a@])@]"
  (pp_list "@ " pp_osym) osyms
  (pp_type ppe) ty  

let add_aptybinding_to_env (env : EcEnv.env) ((osyms, ty) : aptybinding)
      : EcEnv.env =
  let locs =
    List.filter_map
    (omap (fun sym -> (EcIdent.create sym, EcBaseLogic.LD_var (ty, None))))
    osyms in
  let x = EcEnv.LDecl.init env ~locals:(List.rev locs) [] in
  EcEnv.LDecl.toenv x

let add_aptybindings_to_env (env : EcEnv.env) (aptybs : aptybinding list)
      : EcEnv.env =
  List.fold_left add_aptybinding_to_env env aptybs

let pp_aptybindings (ppe : PPEnv.t) (ppf : formatter)
    (aptybs : aptybinding list) : unit =
  fprintf ppf "@[%a@]"
  (pp_list "@ " (pp_aptybinding ppe)) aptybs

let pp_axiom (env : EcEnv.env) (pa : paxiom) : ppna =
  fun (ppf : formatter) ->
    let ue = EcUnify.UniEnv.create None in
    let name = unloc (pa.pa_name) in
    let ptybs_opt = omap (List.map pgtybinding_to_ptybinding) pa.pa_vars in
    let aptybs_opt = omap (abs_ptybindings env ue) ptybs_opt in
    let pf = pa.pa_formula in
    match aptybs_opt with
    | None        ->
        let ppe = PPEnv.ofenv env in
        let f = EcTyping.trans_form_opt env ue pf (Some EcTypes.tbool) in
        let uidmap =
          try EcUnify.UniEnv.close ue with
          | EcUnify.UninstantiateUni -> failure "cannot happen" in
        let ts = EcFol.Tuni.subst uidmap in
        let f = EcFol.Fsubst.f_subst ts f in
        fprintf ppf "@[axiom@ %s@ :@ %a.@]" name 
        (pp_form ppe) f
    | Some aptybs ->
        let ppe = PPEnv.ofenv env in
        let env' = add_aptybindings_to_env env aptybs in
        let ppe' = PPEnv.ofenv env' in
        let f = EcTyping.trans_form_opt env' ue pf (Some EcTypes.tbool) in
        let uidmap =
          try EcUnify.UniEnv.close ue with
          | EcUnify.UninstantiateUni -> failure "cannot happen" in
        let ts = EcFol.Tuni.subst uidmap in
        let subst_ty = EcFol.ty_subst ts in
        let aptybs = aptybindings_type_map subst_ty aptybs in
        let f = EcFol.Fsubst.f_subst ts f in
        fprintf ppf "@[axiom@ %s@ %a@ :@ %a.@]" name 
        (pp_aptybindings ppe) aptybs
        (pp_form ppe') f

let pp_clmode (ppf : formatter) (clm : clmode) : unit =
  match clm with
  | `Alias         -> fprintf ppf "="
  | `Inline `Keep  -> fprintf ppf "<="
  | `Inline `Clear -> fprintf ppf "<-"

let pp_import (ppf : formatter) x : unit =
  match x with
  | `Include -> fprintf ppf "include"
  | `Import  -> fprintf ppf "import"
  | `Export  -> failure "cannot happen"

let qsym_to_sym ((syms, sym) : qsymbol) : symbol =
  if List.is_empty syms then sym else failure "cannot happen"

let by_syntax (x : 'a genoverride * clmode) : 'a * clmode =
  (match fst x with
   | `ByPath _   -> failure "cannot happen"
   | `BySyntax y -> y,
   snd x)

let pp_override (env : EcEnv.env) (ppf : formatter)
    ((pqsym, tho) : pqsymbol * theory_override) : unit =
  let name = unloc pqsym in
  match tho with
  | PTHO_Type tyo ->
      let name = qsym_to_sym name in
      let ue = EcUnify.UniEnv.create None in
      let ppe = PPEnv.ofenv env in
      let ((psyms, pty), clm) = by_syntax tyo in
      let tyvars = List.map unloc psyms in
      let ty = EcTyping.transty EcTyping.tp_tydecl env ue pty in
       (match List.length tyvars with
        | 0 ->
            fprintf ppf "@[type@ %s@ %a@ %a@]" name pp_clmode clm
            (pp_type ppe) ty  
        | 1 ->
            fprintf ppf "@[type@ %s@ %s@ %a@ %a@]" (List.hd tyvars)
            name pp_clmode clm (pp_type ppe) ty  
        | _ ->
            fprintf ppf "@[type@ (%a)@ %s@ %a@ %a@]"
            (pp_list ",@ " pp_symbol) tyvars
            name pp_clmode clm (pp_type ppe) ty)
  | PTHO_Op opo   ->
      let (opod, clm) = by_syntax opo in
      let () = if opod.opov_tyvars <> None then failure "cannot happen" in
      let args = opod.opov_args in
      let pty = opod.opov_retty in
      let pf = opod.opov_body in
      let ue = EcUnify.UniEnv.create None in
      let ty = EcTyping.transty EcTyping.tp_relax env ue pty in
      let args = abs_ptybindings env ue args in
      let env' = add_aptybindings_to_env env args in
      let ppe = PPEnv.ofenv env' in
      let f = EcTyping.trans_form_opt env' ue pf (Some ty) in
      let uidmap =
        try EcUnify.UniEnv.close ue with
        | EcUnify.UninstantiateUni -> failure "cannot happen" in
      let ts = EcFol.Tuni.subst uidmap in
      let subst_ty = EcFol.ty_subst ts in
      let subst_form = EcFol.Fsubst.f_subst ts in
      let args = aptybindings_type_map subst_ty args in
      let ty = subst_ty ty in
      let f = subst_form f in
      (match List.length args with
       | 0 ->
           fprintf ppf "@[op@ %a@ :@ %a@ %a@ %a@]"
           (pp_opname ppe) (EcPath.fromqsymbol name)
           (pp_type ppe) ty pp_clmode clm
           (pp_form ppe) f
       | _ ->
           fprintf ppf "@[op@ %a@ %a@ :@ %a %a@ %a@]"
           (pp_opname ppe) (EcPath.fromqsymbol name)
           (pp_aptybindings ppe) args (pp_type ppe) ty
           pp_clmode clm (pp_form ppe) f)
  | _             -> failure "cannot happen"

let pp_theory_cloning (env : EcEnv.env) (tc : theory_cloning) : ppna =
  fun (ppf : formatter) ->
    let () =
      if tc.pthc_prf <> [] || tc.pthc_rnm <> [] || tc.pthc_clears <> [] ||
         tc.pthc_opts <> [] || tc.pthc_local <> None
      then failure "cannot happen" in
    let import_opt = tc.pthc_import in
    let base = unloc tc.pthc_base in
    let name_opt = omap unloc tc.pthc_name in
    let overs = tc.pthc_ext in
    let ppna_first ppf =
      match import_opt with
      | None        -> fprintf ppf "clone@ %a" pp_qsymbol base
      | Some import ->
          fprintf ppf "clone@ %a@ %a" pp_import import pp_qsymbol base in
    let ppna_second ppf =
      match name_opt with
      | None      -> fprintf ppf "%t" ppna_first
      | Some name -> fprintf ppf "%t@ as@ %s" ppna_first name in
    match List.length overs with
    | 0 -> fprintf ppf "@[%t.@]" ppna_second
    | _ ->
        fprintf ppf
        ("@[%t@ with@\n@ @ @[%a@]@\n" ^^
         "proof *.@\n(* BEGIN USER FILL *)@\n(* END USER FILL *)@]")
        ppna_second (pp_list ",@\n" (pp_override env)) overs

let pp_theory_cloning_uc_changes (env : EcEnv.env) (tc : theory_cloning)
    (uc_of : symbol) (s : symbol) (t : symbol) : ppna =
  fun (ppf : formatter) ->
    let () =
      if tc.pthc_prf <> [] || tc.pthc_rnm <> [] || tc.pthc_clears <> [] ||
         tc.pthc_opts <> [] || tc.pthc_local <> None || tc.pthc_import <> None
      then failure "cannot happen" in
    let uc_as =
      match tc.pthc_name with
      | None      -> failure "cannot happen"
      | Some psym -> unloc psym in
    let overs = tc.pthc_ext in
    let ppna_first ppf = fprintf ppf "clone@ %s@ as@ %s" uc_of uc_as in
    match List.length overs with
    | 0 ->
        fprintf ppf
        ("@[%t@ with@\n@ @ @[op@ %s@ <-@ %s@]@\n" ^^
         "proof *.@\n(* BEGIN USER FILL *)@\n(* END USER FILL *)@]")
        ppna_first s t
    | _ ->
        fprintf ppf
        ("@[%t@ with@\n@ @ @[op@ %s@ <-@ %s@],@\n@ @ @[%a@]@\n" ^^
         "proof *.@\n(* BEGIN USER FILL *)@\n(* END USER FILL *)@]")
        ppna_first s t (pp_list ",@\n" (pp_override env)) overs

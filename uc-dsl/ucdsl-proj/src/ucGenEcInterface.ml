open EcParsetree
open UcMessage

(* shorthands ****************************************************************)
let dl = UcUtils.dummyloc

let dll (l : 'a list) : ('a EcLocation.located) list =
  List.map (fun a -> dl a) l

type qsymbol = EcSymbols.qsymbol

let qs = qsymb_of_symb

let pqs (name : string) = dl (qs name)

let ul = EcLocation.unloc

let ull = EcLocation.unlocs

(*****************************************************************************)

(* strings *******************************************************************)
let sym_and = "/\\"
let sym_or = "\\/"
let sym_eq = "="
let sym_not = "[!]"
let _unit = "unit"
let _option = "option"
let _None = "None"
let _Some = "Some"
let _int = "int"

(*****************************************************************************)

(* UcEcInterface calls *******************************************************)  
let decl_open_theory (name : string) : unit =
  UcEcInterface.process (GthOpen (`Global, false, dl name))

let decl_close_theory (name : string) : unit =
  UcEcInterface.process (GthClose ([], dl name))
  
let decl_operator (pop : poperator) : unit =
  UcEcInterface.process (Goperator pop)

let decl_axiom (pax : paxiom) : unit =
  UcEcInterface.process (Gaxiom pax)
  
let decl_type (ptd : ptydecl) : unit =
  UcEcInterface.process (Gtype [ptd])

let decl_module (pmod : pmodule_def_or_decl) : unit =
  UcEcInterface.process (Gmodule pmod)

let env () = UcEcInterface.env ()
  
let clone (tc : theory_cloning) : unit =
  UcEcInterface.process (GthClone tc)
  
let proof () : unit =
  UcEcInterface.process (Gtactics (`Proof {pm_strict = true}))

let admit () : unit =
  let ptac = 
  {
    pt_core = dl Padmit;
    pt_intros = []
  } in
  UcEcInterface.process (Gtactics (`Actual [ptac]))
  
let qed () : unit =
  UcEcInterface.process (Gsave (dl `Qed))

let proof_admit_qed () : unit =
  proof ();
  admit ();
  qed ()
    
let decl_reduction (red : puserred) : unit =
  UcEcInterface.process (Greduction red)
  
let decl_rewrite (rw : is_local * pqsymbol * pqsymbol list) : unit =
  UcEcInterface.process (Gaddrw rw)
  
let decl_require (threq : threquire) : unit =
  UcEcInterface.process (GthRequire threq)
  
(*****************************************************************************)

(* EcEnv lookups *************************************************************)
let ty_lookup_opt (name : string) : (EcPath.path * EcDecl.tydecl) option =
  let env = env () in
  EcEnv.Ty.lookup_opt (qs name) env
  
let op_lookup_opt (name : string) : (EcPath.path * EcDecl.operator) option =
  let env = env () in
  EcEnv.Op.lookup_opt (qs name) env
  
let ty_lookup (name : string) : (EcPath.path * EcDecl.tydecl) =
  let env = env () in
  EcEnv.Ty.lookup (qs name) env
  
let op_lookup (name : string) : (EcPath.path * EcDecl.operator) =
  let env = env () in
  EcEnv.Op.lookup (qs name) env
  
let mod_lookup (name : string) : 
(EcPath.mpath * (EcModules.module_expr * locality option)) =
  let env = env () in
  EcEnv.Mod.lookup (qs name) env
  
let ax_lookup (name : string) : (EcPath.path * EcDecl.axiom)=
  let env = env () in
  EcEnv.Ax.lookup (qs name) env
(*****************************************************************************)

(* printing ******************************************************************)

let ppe () = EcPrinting.PPEnv.ofenv (env ())

let print_newline (ppf : Format.formatter) : unit =
  Format.fprintf ppf "@."
  
let print_open_theory (ppf : Format.formatter) (name : string) : unit =
  Format.fprintf ppf "@[theory %s.@]@." name;
  print_newline ppf

let print_close_theory (ppf : Format.formatter) (name : string) : unit =
  Format.fprintf ppf "@[end %s.@]@." name;
  print_newline ppf
  
let print_operator (ppf : Format.formatter) (pop : poperator) : unit =
  let name = ul pop.po_name in
  let op = op_lookup name in
  let ppe = ppe () in
  EcPrinting.pp_opdecl ppe ppf op;
  print_newline ppf;
  print_newline ppf

let print_type (ppf : Format.formatter) (name : string) : unit =
  let ppe = ppe() in
  let ptd = ty_lookup name in
  EcPrinting.pp_typedecl ppe ppf ptd;
  print_newline ppf

let print_module (ppf : Format.formatter) (name : string) : unit = 
  let ppe = ppe () in
  let (mpt, (mex, _))  = mod_lookup name in
  EcPrinting.pp_modexp ppe ppf (mpt,mex);
  print_newline ppf
  
let print_axiom (ppf : Format.formatter) (name : string) : unit = 
  let env = env () in
  let ppe = EcPrinting.PPEnv.ofenv env in
  let ax = ax_lookup name in
  EcPrinting.pp_axiom ppe ppf ax;
  print_newline ppf
  
let print_proof_admit_qed (ppf : Format.formatter) : unit =
  Format.fprintf ppf "@[proof.@.@[admit.@]@.qed.@]@."

(*****************************************************************************)

(* writing = declaring + printing ********************************************)
let write_open_theory (ppf : Format.formatter) (name : string) : unit =
  decl_open_theory name;
  print_open_theory ppf name

let write_close_theory (ppf : Format.formatter) (name : string) : unit =
  decl_close_theory name;
  print_close_theory ppf name

let write_operator (ppf : Format.formatter) (pop : poperator) : unit =
  decl_operator pop;
  print_operator ppf pop
  
let write_module (ppf : Format.formatter) (name : string) (pmod : pmodule_def_or_decl) : unit =
  decl_module pmod;
  print_module ppf name

let write_type (ppf : Format.formatter) (ptyd : ptydecl) : unit =
  let name = ul ptyd.pty_name in
  decl_type ptyd;
  print_type ppf name;
  print_newline ppf

let write_lemma (ppf : Format.formatter) (lemma : paxiom) : unit =
  let name = ul lemma.pa_name in
  decl_axiom lemma;
  proof_admit_qed ();
  print_axiom ppf name;
  print_proof_admit_qed ppf;
  print_newline ppf
  
let write_hint_simplify (ppf : Format.formatter) (lname : string) : unit =
  let red = ([`EqTrue], [([pqs lname], None)]) in
  decl_reduction red;
  Format.fprintf ppf "hint simplify [eqtrue] %s.@." lname;
  print_newline ppf

let write_hint_rewrite (ppf : Format.formatter) (rw : string) (lname : string) : unit =
  let hint = (`Global, pqs rw, [pqs lname]) in
  decl_rewrite hint;
  Format.fprintf ppf "hint rewrite %s : %s.@." rw lname;
  print_newline ppf
  
let write_require_import (ppf : Format.formatter) (name : string) : unit =
  let threq = 
    (None,
     [(dl name, None)], (*FIX*)
     Some `Import) in
  decl_require threq;
  Format.fprintf ppf "@[require import %s.@]@." name;
  print_newline ppf
    
(*****************************************************************************)

(* construction of common EcParsetree objects ********************************) 
let record_decl (name : string) (record_fields : precord) : ptydecl =
  let body = PTYD_Record record_fields in
  {
    pty_name   = dl name;
    pty_tyvars = [];
    pty_body   = body;
    pty_locality = `Global;
  }

let datatype_decl (name : string) (ctors : ( psymbol * pty list) list)
: ptydecl =
  {
    pty_name = dl name;
    pty_tyvars = [];
    pty_body = PTYD_Datatype ctors;
    pty_locality = `Global
  }

let qnamed_pty (qname : EcSymbols.qsymbol) : pty = dl (PTnamed (dl qname))

let named_pty (name : string) : pty = qnamed_pty (qs name)

let option_of_pty (pty : pty) : pty = dl (PTapp (pqs _option,[pty]))

let int_pty : pty = named_pty _int

let unit_pty : pty = named_pty _unit

let pex_pqident (pqname : pqsymbol) : pexpr =
  dl (PEident (pqname, None))

let pex_ident (name : string) : pexpr = pex_pqident (pqs name)

let pex_tuple (pexs : pexpr list) : pexpr = dl (PEtuple pexs)

let pex_proj (pex : pexpr) (name : string) = dl (PEproj (pex, pqs name))

let pex_app (ex : pexpr)  (args : pexpr list) : pexpr =
  dl (PEapp (ex,args))
  
let pex_let (pat : plpattern) (wty : pexpr_wty) (pex : pexpr) : pexpr =
  dl (PElet (pat,wty,pex))
 
let pex_if (cond : pexpr) (then_br : pexpr) (else_br : pexpr) : pexpr =
  dl (PEif (cond, then_br, else_br))

let pex_proji (pex : pexpr) (i : int) : pexpr =
  dl (PEproji (pex,i))
  
let pex_match (pex : pexpr) (clauses : (ppattern * pexpr) list) : pexpr =
  dl (PEmatch (pex,clauses))
  
let pex_record (opex : pexpr option) (rcrds : pexpr rfield list) : pexpr =
 dl (PErecord (opex, rcrds))

let pex_or = pex_ident sym_or

let pex_Eq = pex_ident sym_eq

let pex_Not = pex_ident sym_not

let pex_None = pex_ident _None

let pex_Some = pex_ident _Some
  
let pex_and = pex_ident sym_and

let pex_unit = pex_tuple []

let pex_of_int (i : int) : pexpr =
  dl (PEint (EcBigInt.of_int i))
  
let pex_projq (pex : pexpr) (qname : EcSymbols.qsymbol) = 
  dl (PEproj (pex, dl qname))

let ppattern (s : string) (sol : (string option) list) : ppattern =
  PPApp (
    (pqs s, None), 
    dll (List.map (
      (fun so -> 
        match so with
        | None -> None
        | Some s -> Some (dl s)
      )
    ) sol)
  )
  
let ppatSome (str : string) : ppattern =
  ppattern _Some [Some str]

let ppatSome_ : ppattern =
  ppattern _Some [None]
  
let ppatNone : ppattern =
  ppattern _None []
  
let pexpr_cascade (ex : pexpr) (exs : pexpr list) : pexpr =
  match List.length exs with
  | 0 -> failure "Cascade at least one  expression"
  | 1 -> List.hd exs
  | _ ->
    let exs = List.rev exs in
    let last = List.hd exs in
    let rest = List.rev (List.tl exs) in
    List.fold_right ( 
      fun ex1 ex2 -> pex_app ex [ex1; ex2]
    ) rest last


let pex_And (exs : pexpr list) : pexpr =
  pexpr_cascade pex_and exs
  
let pex_Or (exs : pexpr list) : pexpr =
  pexpr_cascade pex_or exs

let pexrfieldq (path : string list) (name : string) (pex : pexpr) 
  : pexpr rfield =
  {
    rf_name  = dl (path, name);
    rf_tvi   = None;
    rf_value = pex;
  }
  
let pexrfield (name : string) (pex : pexpr) : pexpr rfield =
  pexrfieldq [] name pex

let pform_pqident (pqname : pqsymbol) : pformula =
  dl (PFident (pqname, None))
  
let pform_ident (name : string) : pformula =
  pform_pqident (pqs name)

let pf_of_int (i : int) : pformula = 
  dl (PFint (EcBigInt.of_int i))

let pf_0 = dl (PFint EcBigInt.zero)

let pform_tuple (pfs : pformula list) : pformula =
  dl (PFtuple pfs)

let pform_unit = pform_tuple []

let pform_proj (f : pformula) (name : string) : pformula =
  dl (PFproj (f, pqs name))
  
let pform_app (f : pformula) (args : pformula list) : pformula =
  dl (PFapp (f,args))

let abs_oper_pty (name : string) (pty : pty) : poperator =
  let podef = PO_abstr (pty) in
  {
    po_kind     = `Op;
    po_name     = dl name;
    po_aliases  = [];
    po_tags     = [];
    po_tyvars   = None;
    po_args     = [];
    po_def      = podef;
    po_ax       = None;
    po_nosmt    = false;
    po_locality = `Global;
  }
 
let abs_oper_int (name : string) : poperator =  
  abs_oper_pty name int_pty

let op_of_argstyex (name : string) 
(args : (string * pty) list) (tyex : pty) (ex : pexpr) : poperator =
  let podef = PO_concr (tyex, ex) in
  let args = List.map (
    (fun (s,t) -> ([dl (Some (dl s))], t))
  ) args in
  {
    po_kind     = `Op;
    po_name     = dl name;
    po_aliases  = [];
    po_tags     = [];
    po_tyvars   = None;
    po_args     = args;
    po_def      = podef;
    po_ax       = None;
    po_nosmt    = false;
    po_locality = `Global;
  }

let op_of_tyex (name : string) (tyex : pty) (ex : pexpr) : poperator =
  op_of_argstyex name [] tyex ex

let op_of_ex (name : string) (ex : pexpr) : poperator =
  op_of_tyex name (dl PTunivar) ex
  
let oper_int (name : string) (value : int) : poperator =
  op_of_ex name (pex_of_int value)

let paxiom_lemma_varso (name : string) 
(vars : pgtybindings option) (pfrm : pformula) : paxiom =
  {
    pa_name     = dl name;
    pa_tyvars   = None;
    pa_vars     = vars;
    pa_formula  = pfrm;
    pa_kind     = PLemma None;
    pa_nosmt    = false;
    pa_locality = `Global;
  }

let paxiom_lemma_vars (name : string) 
(vars : (string * pty) list) (pfrm : pformula) : paxiom =
  let vars = List.map (
    fun (s,t) -> ([dl (Some (dl s))], PGTY_Type t)
  ) vars in
  paxiom_lemma_varso name (Some vars) pfrm

let paxiom_lemma (name : string) (pfrm : pformula) : paxiom =
  paxiom_lemma_varso name None pfrm
    
let paxiom_axiom (name : string) (pfrm : pformula) : paxiom =
  {
    pa_name     = dl name;
    pa_tyvars   = None;
    pa_vars     = None;
    pa_formula  = pfrm;
    pa_kind     = PAxiom [];
    pa_nosmt    = false;
    pa_locality = `Global;
  }
  
let theory_cloning 
(name : string) (base : string) (opname : string) (opex : pexpr) : theory_cloning =
  let thov = PTHO_Op (`BySyntax {
    opov_nosmt  = false; 
    opov_tyvars = None; opov_args = [];
    opov_retty  = dl PTunivar;
    opov_body   = opex
    }, `Alias) in
  {
    pthc_base   = pqs base;
    pthc_name   = Some (dl name);
    pthc_ext    = [(pqs opname, thov)];
    pthc_prf    = [{pthp_mode = `All (None, []); pthp_tactic = None}];
    pthc_rnm    = [];
    pthc_opts   = [];
    pthc_clears = [];
    pthc_local  = `Global;
    pthc_import = None;
  }
  
let pmodule (def : pmodule_def ) : pmodule_def_or_decl = {
    ptm_locality = `Global;
    ptm_def      = `Concrete def
  }
  
let pmodule_def (name : string) (items : pstructure): pmodule_def = {
    ptm_header = Pmh_ident (dl name);
    ptm_body   = dl (Pm_struct items);
  }
  
let pfunction_decl (name : string) (params : (psymbol * pty) list) (resty : pty)
: pfunction_decl =
  {
    pfd_name     = dl name;
    pfd_tyargs   = Fparams_exp params;
    pfd_tyresult = resty;
    pfd_uses     = (true, None);
  }

let pfunction_body 
  (locals : pfunction_local list) 
  (stmt : pstmt)
  (retval : pexpr option) : pfunction_body =
  {
    pfb_locals = locals;
    pfb_body   = stmt;
    pfb_return = retval;
  }
  
let fun_def (fdecl : pfunction_decl) (fbody : pfunction_body)
: pstructure_item EcLocation.located = dl (Pst_fun (fdecl, fbody))
 
(* ec parsetree instructions *)
let ps_if_then (ifc : pexpr) (ths : pstmt) : pinstr =
  dl (PSif ((ifc,ths),[],[]))

let ps_if_then_else (ifc : pexpr) (ths : pstmt) (els : pstmt) : pinstr =
  dl (PSif ((ifc,ths),[],els))

let ps_assign (a : string) (ex : pexpr) : pinstr =
  dl (PSasgn (dl (PLvSymbol (pqs a)), ex))

let ps_assign_id (a : string) (id : string) : pinstr =
  ps_assign a (pex_ident id)
  
let ps_assignl ( sl : string list) (ex : pexpr) : pinstr =
  let pqssl = List.map (fun s -> pqs s) sl in
  dl (PSasgn (dl (PLvTuple pqssl), ex))
  
let ps_rnd (a : string) (ex : pexpr) : pinstr =
  dl (PSrnd (dl (PLvSymbol (pqs a)), ex))
  
let ps_rndl ( sl : string list) (ex : pexpr) : pinstr =
  let pqssl = List.map (fun s -> pqs s) sl in
  dl (PSrnd (dl (PLvTuple pqssl), ex))
  
let ps_match (mtch_ex : pexpr) (branches : (ppattern * pstmt) list) : pinstr =
  dl (PSmatch (mtch_ex, `Full branches))
  
let ps_call (var : string) (proc : string) (args : pexpr list) : pinstr =
  dl (PScall (
    Some (dl (PLvSymbol (pqs var))),
    dl ([], dl proc),
    dl args 
  ))
  
let pf_var (name : string) (pty : pty) : pfunction_local =
  { 
    pfl_names = dl (`Single, [dl name]);
    pfl_type  = Some pty;
    pfl_init  = None
  }


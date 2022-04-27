open UcSpecTypedSpecCommon
open UcTypedSpec
open EcParsetree
open UcMessage

let stf = Format.std_formatter (*REMOVE*)

let dl = UcUtils.dummyloc

let qs = qsymb_of_symb

let pqs (name : string) = dl (qs name)

let ul = EcLocation.unloc
  
let print_newline (ppf : Format.formatter) : unit =
  Format.fprintf stf "@."; (*REMOVE*)
  Format.fprintf ppf "@."

let decl_open_theory (name : string) : unit =
  UcEcInterface.process (GthOpen (`Global, false, dl name))

let write_open_theory (ppf : Format.formatter) (name : string) : unit =
  decl_open_theory name;
  Format.fprintf stf "@[theory %s.@]@." name; (*REMOVE*)
  Format.fprintf ppf "@[theory %s.@]@." name;
  print_newline ppf

let decl_close_theory (name : string) : unit =
  UcEcInterface.process (GthClose ([], dl name))
  
let write_close_theory (ppf : Format.formatter) (name : string) : unit =
  decl_close_theory name;
  Format.fprintf stf "@[end %s.@]@." name; (*REMOVE*)
  Format.fprintf ppf "@[end %s.@]@." name;
  print_newline ppf

let decl_operator (pop : poperator) : unit =
  UcEcInterface.process (Goperator pop)

let print_operator (ppf : Format.formatter) (pop : poperator) : unit =
  let name = ul pop.po_name in
  let env = UcEcInterface.env () in
  let ppe = EcPrinting.PPEnv.ofenv env in
  let op = EcEnv.Op.lookup (qs name) env in
  EcPrinting.pp_opdecl ppe stf op; (*REMOVE*)
  EcPrinting.pp_opdecl ppe ppf op;
  print_newline ppf;
  print_newline ppf

let write_operator (ppf : Format.formatter) (pop : poperator) : unit =
  decl_operator pop;
  print_operator ppf pop

let decl_axiom (pax : paxiom) : unit =
  UcEcInterface.process (Gaxiom pax)
  
let decl_type (ptd : ptydecl) : unit =
  UcEcInterface.process (Gtype [ptd])
  
let print_type (ppf : Format.formatter) (name : string) : unit =
  let env = UcEcInterface.env () in
  let ppe = EcPrinting.PPEnv.ofenv env in
  let ptd = EcEnv.Ty.lookup (qs name) env in
  EcPrinting.pp_typedecl ppe stf ptd; (*REMOVE*)
  EcPrinting.pp_typedecl ppe ppf ptd;
  print_newline ppf

let decl_module (pmod : pmodule_def_or_decl) : unit =
  UcEcInterface.process (Gmodule pmod)

let print_module (ppf : Format.formatter) (name : string) : unit = 
  let env = UcEcInterface.env () in
  let ppe = EcPrinting.PPEnv.ofenv env in
  let (mpt, (mex, _))  = EcEnv.Mod.lookup (qs name) env in
  EcPrinting.pp_modexp ppe stf (mpt,mex); (*REMOVE*)
  EcPrinting.pp_modexp ppe ppf (mpt,mex);
  print_newline ppf
  
let write_module (ppf : Format.formatter) (name : string) (pmod : pmodule_def_or_decl) : unit =
  decl_module pmod;
  print_module ppf name
  
let print_theory (ppf : Format.formatter) (name : string) : unit = 
  let env = UcEcInterface.env () in
  let ppe = EcPrinting.PPEnv.ofenv env in
  let pth = EcEnv.Theory.lookup (qs name) env in
  EcPrinting.pp_theory ppe stf pth; (*REMOVE*)
  EcPrinting.pp_theory ppe ppf pth;
  print_newline ppf

let print_axiom (ppf : Format.formatter) (name : string) : unit = 
  let env = UcEcInterface.env () in
  let ppe = EcPrinting.PPEnv.ofenv env in
  let ax = EcEnv.Ax.lookup (qs name) env in
  EcPrinting.pp_axiom ppe stf ax; (*REMOVE*)
  EcPrinting.pp_axiom ppe ppf ax;
  print_newline ppf

let ty_lookup (name : string) : (EcPath.path * EcDecl.tydecl) =
  let env = UcEcInterface.env () in
  EcEnv.Ty.lookup (qs name) env

let named_pty (name : string) = dl (PTnamed (pqs name))

let option_of_pty (pty : pty) = dl (PTapp (pqs "option",[pty]))

let option_of_pty_name (name : string) = option_of_pty (named_pty name)

let addr_pty = named_pty "addr"

let port_pty = named_pty "port"

let msg_pty = named_pty "msg"

let int_pty = named_pty "int"

let unit_pty = named_pty "unit"
  
let abs_oper_int (name : string) : poperator =  
  let podef = PO_abstr (int_pty) in
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

let opname_pi = "pi"
  
let pi_op : poperator = abs_oper_int opname_pi

let opname_adv_if_pi = "_adv_if_pi"

let axname_adv_if_pi_gt0 = "_adv_if_pi_gt0"

let pform_ident (name : string) : pformula =
  dl (PFident (pqs name, None))

let pf_of_int (i : int) : pformula = 
  dl (PFint (EcBigInt.of_int i))

let pf_0 = dl (PFint EcBigInt.zero)

let axiom_adv_if_pi_gt0 : paxiom =
  let f_le = pform_ident "<" in
  let f_ax = pform_ident opname_adv_if_pi in 
  let pfrm = dl (PFapp (f_le,[pf_0; f_ax])) in 
  {
    pa_name     = dl axname_adv_if_pi_gt0;
    pa_tyvars   = None;
    pa_vars     = None;
    pa_formula  = pfrm;
    pa_kind     = PAxiom [];
    pa_nosmt    = false;
    pa_locality = `Global;
  }

let name_record_func (msg_name : string) : string = msg_name^"___func"

let name_record_adv (msg_name : string) : string = msg_name^"___adv"

let name_record (msg_name : string) (param_name : string) : string = msg_name^"__"^param_name

let name_record_dir_port (name : string)  (mb : message_body_tyd) : string =
  name_record name (EcUtils.oget mb.port)
 
let params_map_to_list (pm : ty_index IdMap.t) : (string * pty) list =
  let bpm = IdMap.bindings pm in
  let bpm = List.map (fun (s,ti) -> (s, ul ti)) bpm in
  let bpm_ord = List.sort (fun (_,(_,i1)) (_,(_,i2)) -> i1-i2) bpm in
  List.map (fun (name,((_,pty),_)) -> (name, pty)) bpm_ord
  
let isdirect (mb : message_body_tyd) : bool =
  match mb.port with
  | None -> false
  | Some _ -> true

let msg_type (name : string) (mb : message_body_tyd) : ptydecl =
  let msg_data = List.map (fun (s,t) -> (dl (name_record name s), t)) 
    (params_map_to_list mb.params_map) in
  let self_addr = (dl (name_record_func name), addr_pty) in
  let other_port =
    if (isdirect mb)
    then (dl (name_record_dir_port name mb), port_pty)
    else (dl (name_record_adv name), addr_pty)
    in
  let body = PTYD_Record (self_addr :: other_port :: msg_data) in
  {
    pty_name   = dl name;
    pty_tyvars = [];
    pty_body   = body;
    pty_locality = `Global;
  }
  
let write_type (ppf : Format.formatter) (ptyd : ptydecl) : unit =
  let name = ul ptyd.pty_name in
  decl_type ptyd;
  print_type ppf name;
  print_newline ppf

let enc_op_name (name : string) : string = "enc_"^name

let pex_ident (name : string) : pexpr = dl (PEident (pqs name, None))

let pex_Dir = pex_ident "Dir"

let pex_Adv = pex_ident "Adv"

let pex_true = pex_ident "true"

let pex_tuple (pexs : pexpr list) : pexpr = dl (PEtuple pexs)

let pex_proj (pex : pexpr) (name : string) = dl (PEproj (pex, pqs name))

let pex_app (ex : pexpr)  (args : pexpr list) : pexpr =
  dl (PEapp (ex,args))

let epdp_ty_univ_name (ty_name : string) : string =
  match ty_name with
  | "unit" -> "epdp_unit_univ"
  | "bool" -> "epdp_bool_univ"
  | "int"  -> "epdp_int_univ"
  | "addr" -> "epdp_addr_univ"
  | "port" -> "epdp_port_univ"
  | "univ" -> "epdp_id"
  | _ -> failure ("yet unsupported epdp for "^ty_name)

let epdp_name_univ (name : string) : pexpr =
  pex_ident (epdp_ty_univ_name name)

let epdp_tuple_name (arity : int) : string =
  match arity with
  | 2 -> "epdp_pair_univ"
  | 3 -> "epdp_tuple3_univ"
  | 4 -> "epdp_tuple4_univ"
  | 5 -> "epdp_tuple5_univ"
  | 6 -> "epdp_tuple6_univ"
  | 7 -> "epdp_tuple7_univ"
  | 8 -> "epdp_tuple8_univ"
  | _ -> failure "epdp_tuples must have size between 2 and 8"

let epdp_app_name (name : string) : string =
  match name with
  | "choice" -> "epdp_choice_univ"
  | "choice3" -> "epdp_choice3_univ"
  | "choice4" -> "epdp_choice4_univ"
  | "choice5" -> "epdp_choice5_univ"
  | "choice6" -> "epdp_choice6_univ"
  | "choice7" -> "epdp_choice7_univ"
  | "choice8" -> "epdp_choice8_univ"
  | "option"  -> "epdp_option_univ"
  | "list"    -> "epdp_list_univ"
  | _ -> failure "supported parametric types are: choice,..., choice8, option, list"

let rec epdp_pty_univ (t : pty) : pexpr =
  match ul t with
  | PTtuple  ptys -> epdp_tuple_univ ptys
  | PTnamed  pqs  -> let (_, name) = ul pqs in epdp_name_univ name
  | PTapp (pqs, ptys) -> let (_, name) = ul pqs in epdp_app_univ name ptys 
  | _ -> failure ("Only tuples, named types, and parametric types choice,..., choice8, option, list  are supported." )
and epdp_tuple_univ (ptys : pty list) : pexpr =
  let epdp_name = epdp_tuple_name (List.length ptys) in
  pex_app (pex_ident epdp_name) (List.map (fun t -> epdp_pty_univ t) ptys)
and epdp_app_univ (name : string) (ptys : pty list) : pexpr =
  let epdp_name = epdp_app_name name in
  pex_app (pex_ident epdp_name) (List.map (fun t -> epdp_pty_univ t) ptys)

let epdp_data_univ (params_map : ty_index IdMap.t) : pexpr =
  let ptys = List.map (fun (_,pty) -> pty) (params_map_to_list params_map) in
  match ptys with
  | [] -> pex_ident "epdp_unit_univ"
  | [t] -> epdp_pty_univ t
  | _ -> epdp_tuple_univ ptys

let pex_unit = pex_tuple []
  
let enc_args (var_name : string) (msg_name : string ) (params_map : ty_index IdMap.t) : pexpr =
  let pns = fst (List.split (params_map_to_list params_map)) in
  if pns = []
  then pex_unit
  else pex_tuple (List.map (fun pn -> pex_proj (pex_ident var_name) (name_record msg_name pn)) pns)

let enc_u (var_name : string) (msg_name : string) (params_map : ty_index IdMap.t) : pexpr =
  let ex = pex_proj (epdp_data_univ params_map) "enc" in
  let args = enc_args var_name msg_name params_map in
  pex_app ex [args]

let pex_of_int (i : int) : pexpr =
  dl (PEint (EcBigInt.of_int i))

let enc_op (tag : int) (mty_name : string) (mb : message_body_tyd) : poperator =
  let var_name = "x" in
  let u = enc_u var_name mty_name mb.params_map in
  let selfport = pex_tuple [
    pex_proj (pex_ident var_name) (name_record_func mty_name); 
    pex_ident opname_pi ] in
  let isdirect = isdirect mb in
  let otherport = 
    if isdirect
    then pex_proj (pex_ident var_name) (name_record_dir_port mty_name mb) 
    else pex_tuple [
      pex_proj (pex_ident var_name) (name_record_adv mty_name); 
      pex_ident opname_adv_if_pi ]
    in
  let ptsource = if mb.dir = In then otherport else selfport in
  let ptdest = if mb.dir = In then selfport else otherport in
  let mode = if isdirect then pex_Dir else pex_Adv in
  let encex = pex_tuple [mode; ptdest; ptsource; pex_of_int tag; u] in
  let args = [([dl(Some (dl var_name))], named_pty mty_name) ] in
  let def = PO_concr (msg_pty, encex) in
  {
    po_kind     = `Op;
    po_name     = dl (enc_op_name mty_name);
    po_aliases  = [];
    po_tags     = [];
    po_tyvars   = None;
    po_args     = args;
    po_def      = def;
    po_ax       = None;
    po_nosmt    = false;
    po_locality = `Global;
  }

let dec_op_name (name : string) : string = "dec_"^name

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

let pex_or = pex_ident "\\/"

let pex_Eq = pex_ident "="

let pex_Not = pex_ident "[!]"

let pex_None = pex_ident "None"

let pex_Some = pex_ident "Some"

let pexrfield (name : string) (pex : pexpr) : pexpr rfield =
  {
    rf_name  = pqs name;
    rf_tvi   = None;
    rf_value = pex;
  }

(* strings *******************************************************************)
let __self = "_self"
let __adv = "_adv"
let __st = "_st"
let _init = "init"
let _self_ = "self_"
let _adv_ = "adv_"
let _invoke = "invoke"
let _m = "m"
let __m = "_m"
let _r = "r"
let __r = "_r"
let _parties = "parties"
let _dec = "dec"
let _enc = "enc"
let __x = "_x"
let _envport = "envport"
let _and = "/\\"
let _UC__IF = "UC__IF"
(*****************************************************************************)

(* ec parsetree expressions **************************************************)
let pex_and = pex_ident _and

let pex_m = pex_ident _m

let pex__self = pex_ident __self

let pex__adv = pex_ident __adv

let pex_projq (pex : pexpr) (qname : EcSymbols.qsymbol) = 
  dl (PEproj (pex, dl qname))

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

let pex_envport = pex_ident _envport

let pex_app_envport (arg : pexpr) : pexpr =
  pex_app pex_envport [
    pex__self;
    pex__adv;
    arg;
  ]

(*TODO merge code with pexrfield *)  
let pexrfieldq (path : string list) (name : string) (pex : pexpr) 
  : pexpr rfield =
  {
    rf_name  = dl (path, name);
    rf_tvi   = None;
    rf_value = pex;
  }
(*****************************************************************************)

let dec_op (tag : int) (mty_name : string) (mb : message_body_tyd) : poperator =
  let var_name = "m" in
  let mode = "mod" in
  let pt1 = "pt1" in
  let pt2 = "pt2" in
  let funcport = if mb.dir = In then pt1 else pt2 in
  let otherport = if mb.dir = In then pt2 else pt1 in 
  let _tag = "tag" in
  let v = "v" in
  let osym (name : string) = dl (Some (dl name)) in
  let pat = dl (LPTuple [osym mode; osym pt1; osym pt2; osym _tag; osym v]) in
  
  let wty = (pex_ident var_name, None) in
  let isdirect = isdirect mb in
  let notmode = if isdirect then pex_Adv else pex_Dir in
  let if1 = pex_app pex_Eq [pex_ident mode; notmode] in
  let no0 = pex_app pex_Not 
    [pex_app pex_Eq [pex_proji (pex_ident otherport) 1; pex_ident opname_adv_if_pi]] in
  let no1 = pex_app pex_Not 
    [pex_app pex_Eq [pex_proji (pex_ident funcport) 1; pex_ident opname_pi]] in
  let no2 = pex_app pex_Not [pex_app pex_Eq [pex_ident _tag; pex_of_int tag]] in
  let if_cond = 
    if isdirect
    then pex_tuple [pex_Or [if1; no1; no2]] 
    else pex_tuple [pex_Or [if1; no0; no1; no2]] in
  
  let p = "p" in
  let n' (pn : string) : string = pn^"'" in
  let pns = fst (List.split (params_map_to_list mb.params_map)) in
  let patm = dl (LPTuple (List.map (fun pn -> osym (n' pn)) pns)) in
  let wtym = (pex_ident p, None) in
  let funcfld = pexrfield (name_record_func mty_name) (pex_proji (pex_ident funcport) 0) in
  let otherfld = 
    if isdirect
    then pexrfield (name_record_dir_port mty_name mb) (pex_ident otherport) 
    else pexrfield (name_record_adv mty_name) (pex_proji (pex_ident otherport) 0)
    in
  let dataflds = List.map 
    (fun pn -> pexrfield (name_record mty_name pn) (pex_ident (n' pn)) ) 
    pns in
  let msg = pex_record None (funcfld::otherfld::dataflds) in
  let omsg = pex_app pex_Some [msg] in

  let ex2 = 
    if pns = [] 
    then omsg
    else pex_let patm wtym omsg  in
  let pat2 = 
    if pns = []
    then PPApp ((pqs "Some", None), [dl None])
    else PPApp ((pqs "Some", None), [dl(Some (dl p))]) in
  let mtch2 = (pat2, ex2) in

  let pat1 = PPApp ((pqs "None", None), []) in
  let mtch1 = (pat1, pex_None) in

  let dd = pex_proj (epdp_data_univ mb.params_map) "dec" in
  let pmex = pex_app dd [pex_ident v] in
  let else_br = pex_match pmex [mtch1; mtch2] in

  let pif = pex_if if_cond pex_None else_br in
  
  let decex = pex_let pat wty pif in
  let args = [([dl(Some (dl var_name))], msg_pty) ] in
  let ret_pty = option_of_pty_name mty_name in

  let def = PO_concr (ret_pty, decex) in
  {
    po_kind     = `Op;
    po_name     = dl (dec_op_name mty_name);
    po_aliases  = [];
    po_tags     = [];
    po_tyvars   = None;
    po_args     = args;
    po_def      = def;
    po_ax       = None;
    po_nosmt    = true;
    po_locality = `Global;
  }

let name_epdp_op (mty_name : string) : string = "epdp_"^mty_name

let epdp_op (mty_name : string) : poperator =
  let enc = pexrfield "enc" (pex_ident (enc_op_name mty_name)) in
  let dec = pexrfield "dec" (pex_ident (dec_op_name mty_name)) in
  let epdp = pex_record None [enc; dec] in
  let def = PO_concr (dl PTunivar, epdp) in
  {
    po_kind     = `Op;
    po_name     = dl (name_epdp_op mty_name);
    po_aliases  = [];
    po_tags     = [];
    po_tyvars   = None;
    po_args     = [];
    po_def      = def;
    po_ax       = None;
    po_nosmt    = false;
    po_locality = `Global;
  }

let name_lemma_epdp_valid (name : string) : string =
  "valid_epdp_"^name

let lemma_epdp (name : string) : paxiom =
  let f_ve = pform_ident "valid_epdp" in
  let f_e = pform_ident (name_epdp_op name) in
  let pfrm = dl (PFapp (f_ve, [f_e])) in 
  {
    pa_name     = dl (name_lemma_epdp_valid name);
    pa_tyvars   = None;
    pa_vars     = None;
    pa_formula  = pfrm;
    pa_kind     = PLemma None;
    pa_nosmt    = false;
    pa_locality = `Global;
  }

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
  
let print_proof_admit_qed (ppf : Format.formatter) : unit =
  Format.fprintf stf "@[proof.@.@[admit.@]@.qed.@]@."; (*REMOVE*)
  Format.fprintf ppf "@[proof.@.@[admit.@]@.qed.@]@."

let write_lemma (ppf : Format.formatter) (lemma : paxiom) : unit =
  let name = ul lemma.pa_name in
  decl_axiom lemma;
  proof_admit_qed ();
  print_axiom ppf name;
  print_proof_admit_qed ppf;
  print_newline ppf
    
let write_hint_simplify_epdp (ppf : Format.formatter) (name : string) : unit =
  let lname = name_lemma_epdp_valid name in
  let red = ([`EqTrue], [([pqs lname], None)]) in
  UcEcInterface.process (Greduction red);
  Format.fprintf stf "hint simplify [eqtrue] %s.@." lname; (*REMOVE*)
  Format.fprintf ppf "hint simplify [eqtrue] %s.@." lname;
  print_newline ppf
  
let write_hint_rewrite_epdp (ppf : Format.formatter) (name : string) : unit =
  let lname = name_lemma_epdp_valid name in
  let rw = (`Global, pqs "epdp", [pqs lname]) in
  UcEcInterface.process (Gaddrw rw);
  Format.fprintf stf "hint rewrite epdp : %s.@." lname; (*REMOVE*)
  Format.fprintf ppf "hint rewrite epdp : %s.@." lname;
  print_newline ppf

let epdp_name_univ_form (name : string) : pformula =
  pform_ident (epdp_ty_univ_name name)

  
let pform_tuple (pfs : pformula list) : pformula =
  dl (PFtuple pfs)

let pform_unit = pform_tuple []

let pform_proj (f : pformula) (name : string) : pformula =
  dl (PFproj (f, pqs name))
  
let pform_app (f : pformula) (args : pformula list) : pformula =
  dl (PFapp (f,args))
    
let rec epdp_pty_univ_form (t : pty) : pformula =
  match ul t with
  | PTtuple  ptys -> epdp_tuple_univ_form ptys
  | PTnamed  pqs  -> let (_, name) = ul pqs in epdp_name_univ_form name
  | PTapp (pqs, ptys) -> let (_, name) = ul pqs in epdp_app_univ_form name ptys 
  | _ -> failure ("Only tuples, named types, and parametric types choice,..., choice8, option, list  are supported." )
and epdp_tuple_univ_form (ptys : pty list) : pformula =
  let epdp_name = epdp_tuple_name (List.length ptys) in
  pform_app (pform_ident epdp_name) (List.map (fun t -> epdp_pty_univ_form t) ptys)
and epdp_app_univ_form (name : string) (ptys : pty list) : pformula =
  let epdp_name = epdp_app_name name in
  pform_app (pform_ident epdp_name) (List.map (fun t -> epdp_pty_univ_form t) ptys)

let epdp_data_univ_form (params_map : ty_index IdMap.t) : pformula =
  let ptys = List.map (fun (_,pty) -> pty) (params_map_to_list params_map) in
  match ptys with
  | [] -> pform_ident "epdp_unit_univ"
  | [t] -> epdp_pty_univ_form t
  | _ -> epdp_tuple_univ_form ptys
  
let enc_args_form (var_name : string) (msg_name : string ) (params_map : ty_index IdMap.t) : pformula =
  let pns = fst (List.split (params_map_to_list params_map)) in
  if pns = []
  then pform_unit
  else pform_tuple (List.map (fun pn -> pform_proj (pform_ident var_name) (name_record msg_name pn)) pns)

let enc_u_form (var_name : string) (msg_name : string) (params_map : ty_index IdMap.t) : pformula =
  let f = pform_proj (epdp_data_univ_form params_map) "enc" in
  let args = enc_args_form var_name msg_name params_map in
  pform_app f [args]

let name_lemma_eq_of_valid (name : string) : string =
  "eq_of_valid_"^name

let pform_true = pform_ident "true"

let pform_Dir = pform_ident "Dir"

let pform_Adv = pform_ident "Adv"

let lemma_eq_of_valid (tag : int) (mty_name : string) (mb : message_body_tyd) : paxiom =
  let m = "m" in
  let vars = Some [([dl (Some (dl m))], PGTY_Type msg_pty)] in
  
  let fepdp = pform_ident (name_epdp_op mty_name) in
  let fm = pform_ident m in
  let f_l = dl (PFapp (pform_ident "is_valid", [fepdp; fm])) in
  let f_eq = pform_ident "=" in
  let fdec = dl (PFtuple [dl (PFapp (dl (PFproj (fepdp, pqs "dec" )),[fm]))]) in 
  let foget = dl (PFapp (pform_ident "oget",[fdec])) in
  
  let x = "x" in
  let fx = pform_ident x in
  let isdirect = isdirect mb in
  let fmode = if isdirect then pform_Dir else pform_Adv in (*TODO isdirect from mb*)
  let fsadd = dl (PFproj (fx, pqs (name_record_func mty_name))) in
  let funcport = dl (PFtuple [fsadd; pform_ident opname_pi]) in
  let otherport = 
    if isdirect
    then dl (PFproj (fx, pqs (name_record_dir_port mty_name mb)))
    else let fsadv = dl (PFproj (fx, pqs (name_record_adv mty_name))) in
      dl (PFtuple [fsadv; pform_ident opname_adv_if_pi])
    in
  let fdport = if mb.dir = In then funcport else otherport in
  let fsport = if mb.dir = In then otherport else funcport in
  let fdata = enc_u_form x mty_name mb.params_map in
  let fmsg = dl (PFtuple [fmode; fdport; fsport; pf_of_int tag; fdata] ) in
  
  let flet = dl (PFlet (dl (LPSymbol (dl "x")), (foget, None), fmsg)) in
  let f_r = pform_app f_eq [fm; flet] in
  let f_imp = pform_ident "=>" in
  let pfrm = pform_app f_imp [f_l; f_r] in 
  {
    pa_name     = dl (name_lemma_eq_of_valid mty_name);
    pa_tyvars   = None;
    pa_vars     = vars;
    pa_formula  = pfrm;
    pa_kind     = PLemma None;
    pa_nosmt    = false;
    pa_locality = `Global;
  }

let write_message (ppf : Format.formatter) (tag : int) (name : string) (mb : message_body_tyd) : unit =
  write_type ppf (msg_type name mb);
  write_operator ppf (enc_op tag name mb);
  write_operator ppf (dec_op tag name mb);
  write_operator ppf (epdp_op name);
  write_lemma ppf (lemma_epdp name);
  write_hint_simplify_epdp ppf name;
  write_hint_rewrite_epdp ppf name;
  write_lemma ppf (lemma_eq_of_valid tag name mb)
  
let oper_int (name : string) (value : int) : poperator =  
  let podef = PO_concr (dl PTunivar, pex_of_int value) in
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
  
let pi_op2 = oper_int opname_pi 2

let uc_name (name : string) : string =
  "UC_"^name
  
let write_basic_int 
  (ppf : Format.formatter) 
  (isdirect : bool) 
  (is4ideal : bool) 
  (name : string) 
  (bibt : basic_inter_body_tyd) 
  : unit =
  let name = uc_name name in
  write_open_theory ppf name;
  if (isdirect || (not is4ideal))
  then write_operator ppf pi_op
  else write_operator ppf pi_op2
  ;
  let bibtl = IdMap.bindings bibt in
  List.iteri (fun i (n, mb) -> write_message ppf i n mb) bibtl;
  write_close_theory ppf name

let state_type_name = "_state"

let state_name (name : string) : string = "_State_"^name

let state_type (states : state_tyd IdMap.t) : ptydecl =
  let s2e (sname, sbod : string * state_tyd) : (psymbol * pty list) =
    let sptys = snd (List.split (params_map_to_list (ul sbod).params)) in
    (dl (state_name sname), sptys)
  in
  let ste = List.map s2e (IdMap.bindings states) in
  {
    pty_name = dl state_type_name;
    pty_tyvars = [];
    pty_body = PTYD_Datatype ste;
    pty_locality = `Global
  }


(* ec parsetree declarations *************************************************)
let pmodule (def : pmodule_def ) : pmodule_def_or_decl = {
    ptm_locality = `Global;
    ptm_def      = `Concrete def
  }
  
let pmodule_def (name : string) (items : pstructure): pmodule_def = {
    ptm_header = Pmh_ident (dl name);
    ptm_body   = dl (Pm_struct items);
  }
(*****************************************************************************)

(* ec parsetree instructions *************************************************)  
let ps_if_then (ifc : pexpr) (ths : pstmt) : pinstr =
  dl (PSif ((ifc,ths),[],[]))

let ps_if_then_else (ifc : pexpr) (ths : pstmt) (els : pstmt) : pinstr =
  dl (PSif ((ifc,ths),[],els))

let ps_assign (a : string) (ex : pexpr) : pinstr =
  dl (PSasgn (dl (PLvSymbol (pqs a)), ex))

let ps_assign_id (a : string) (id : string) : pinstr =
  ps_assign a (pex_ident id)
  
let ps_match (mtch_ex : pexpr) (branches : (ppattern * pstmt) list) : pinstr =
  dl (PSmatch (mtch_ex, `Full branches))
(*****************************************************************************)

(* uc instruction to ec statement translation ********************************)
type locals = { vals : pexpr IdMap.t }

type interfaces = {
  di_name : string;
  di      : basic_inter_body_tyd IdMap.t;
  ai_name : string;
  ai      : basic_inter_body_tyd;
}

let get_message_body 
  (interfaces : interfaces) 
  (inter_id_path : string list) 
  (msgtyname : string) 
  : message_body_tyd =
  match inter_id_path with
  | [name; bin] when name = interfaces.di_name -> 
      IdMap.find msgtyname (IdMap.find bin interfaces.di)
  | [name] when name = interfaces.ai_name -> 
      IdMap.find msgtyname interfaces.ai
  | _ -> failure "impossible, ideal fun cannot have other inter_id_path"

(*TODO merge code with dec op*)
let mk_message_record_ex
  (inter_id_path : string list) 
  (msgtyname : string)
  (mb : message_body_tyd)
  (port : pexpr option)
  (data : pexpr list)
  : pexpr =
  let pexrfield_iip = pexrfieldq inter_id_path in
  let funcfld = pexrfield_iip (name_record_func msgtyname) (pex_ident __self) in  
  let otherfld = 
    match (mb.port, port) with
    | (None, None) ->
      pexrfield_iip (name_record_adv msgtyname) (pex_ident __adv)
    | (Some mp, Some p) ->
      pexrfield_iip (name_record_dir_port msgtyname mb) p
    | _ -> 
      failure "mb.port and port should either both be None or both Some" in
  let pns = fst (List.split (params_map_to_list mb.params_map)) in
  let dataflds = List.map2
    (fun pn ex -> pexrfield_iip (name_record msgtyname pn) ex) 
    pns data in
  pex_record None (funcfld::otherfld::dataflds)


let rec uc2ec_expr (locals : locals) (uc_expr : pexpr) : pexpr =
  let uc_ec_expr = uc2ec_expr locals in
  match ul uc_expr with
  | PEapp (
      {
        pl_loc  = _;
        pl_desc = PEident (
            {
              pl_loc  = _;
              pl_desc = ([], _envport);
            },
            None
          );
      },
      [arg]) -> 
    pex_app_envport (uc_ec_expr arg)
  | PEident (pqsymbol, ptyannoto) ->
    begin match ((ul pqsymbol), ptyannoto) with
    | (([],s), None) when IdMap.mem s locals.vals -> IdMap.find s locals.vals      
    | _ -> dl (PEident (pqsymbol, ptyannoto))
    end
  | PEcast (pexpr, pty) -> 
    dl (PEcast (uc_ec_expr pexpr, pty))
  | PEint    zint -> 
    dl (PEint zint)
  | PEdecimal (zint, (i, zint2)) -> 
    dl (PEdecimal (zint, (i, zint2)))
  | PEapp (pexpr, pexprl) -> 
    dl (PEapp (uc_ec_expr pexpr, List.map uc_ec_expr pexprl))
  | PElet (plpattern, (pexw, ptyo), pexpr) -> 
    dl (PElet (plpattern, (uc_ec_expr pexw, ptyo), uc_ec_expr pexpr))
  | PEtuple  pexprl ->
    dl (PEtuple (List.map uc_ec_expr pexprl))
  | PEif (pexc, pexif, pexel) ->
    dl (PEif (uc_ec_expr pexc, uc_ec_expr pexif, uc_ec_expr pexel))
  | PEmatch (pexpr, patexl) ->
    dl (PEmatch (
      uc_ec_expr pexpr, 
      List.map (fun (pat,ex) -> (pat, uc_ec_expr ex)) patexl))
  | PEforall (ptybindings, pexpr) ->
    dl (PEforall (ptybindings, uc_ec_expr pexpr))
  | PEexists (ptybindings, pexpr) ->
    dl (PEexists (ptybindings, uc_ec_expr pexpr))
  | PElambda (ptybindings, pexpr) ->
    dl (PElambda (ptybindings, uc_ec_expr pexpr))
  | PErecord (pexpro, pexprrl) ->
    let uc_ec_exprr (pexprr : pexpr rfield) : pexpr rfield =
      {
        rf_name  = pexprr.rf_name;
        rf_tvi   = pexprr.rf_tvi;
        rf_value = uc_ec_expr pexprr.rf_value;
      }
    in
    dl (PErecord (pexpro, List.map uc_ec_exprr pexprrl))
  | PEproj (pexpr, pqsymbol) ->
    dl (PEproj (uc_ec_expr pexpr, pqsymbol))
  | PEproji (pexpr, i) ->
    dl (PEproji (uc_ec_expr pexpr, i))
  | PEscope (pqsymbol, pexpr) ->
    dl (PEscope (pqsymbol, uc_ec_expr pexpr))

let uc_inter_path (path : string list) : string list =
 if path = [] then []
 else 
   let hd = uc_name (List.hd path) in
   let tl = List.tl path in
   hd::tl 

let rec uc2ec_stmt (locals : locals) (interfaces : interfaces) (inst : instruction_tyd) : pstmt =
  match ul inst with
  | Assign (lhs, pexpr) -> []
  | Sample (lhs, pexpr) -> []
  | ITE (pexpr, instruction_tyd_ll, instruction_tyd_llo) ->
     ucITE2ec_stmt locals interfaces pexpr instruction_tyd_ll instruction_tyd_llo
  | Match (pexpr, match_clause_tyd_ll) -> []
  | SendAndTransition send_and_transition_tyd ->
     ucSandT2ec_stmt locals interfaces send_and_transition_tyd
  | Fail -> []
                
and uc_inst_list2ec_stmt 
  (locals : locals)
  (interfaces : interfaces)
  (uc_instll : instruction_tyd list EcLocation.located) 
  : pstmt =
  List.concat (List.map (uc2ec_stmt locals interfaces) (ul uc_instll))
  
and ucITE2ec_stmt (locals : locals) (interfaces : interfaces)
  (cond : pexpr) 
  (if_br : instruction_tyd list EcLocation.located) 
  (else_bro : instruction_tyd list EcLocation.located option)
  : pstmt =
  let cond = uc2ec_expr locals cond in
  let if_br = uc_inst_list2ec_stmt locals interfaces if_br in
  match else_bro with
  | Some else_br ->
    let else_br = uc_inst_list2ec_stmt locals interfaces else_br in
    [ps_if_then_else cond if_br else_br]
  | None ->
    [ps_if_then cond if_br]
    
and ucSandT2ec_stmt 
  (locals : locals)
  (interfaces : interfaces)
  (s_and_t : send_and_transition_tyd) 
  : pstmt =
  let send locals interfaces (msg_ex : msg_expr_tyd) : pinstr =
    let iip = uc_inter_path (ul msg_ex.path).inter_id_path in
    let mtn = (ul msg_ex.path).msg in
    let mb = get_message_body interfaces iip mtn in
    let porto =
      match msg_ex.port_expr with
      | None -> None
      | Some p -> Some (uc2ec_expr locals p) in
    let args = List.map (fun ex -> uc2ec_expr locals ex) (ul msg_ex.args) in
    let msg = mk_message_record_ex iip mtn mb porto args in
    let epdp_path = (iip, name_epdp_op mtn) in
    let encmsg = (*TODO merge with mminstr code *)
      pex_app (pex_proj (dl (PEident (dl (epdp_path), None))) _enc) [msg] in
    let msgo = pex_app pex_Some [encmsg] in
    ps_assign __r msgo
  in
  let transition (locals : locals) (st_ex : state_expr_tyd ) : pinstr =
    let args = List.map (fun ex -> uc2ec_expr locals ex) (ul st_ex.args) in
    let st_id = state_name (ul st_ex.id) in
    let st = 
      if args = []
      then pex_ident st_id
      else pex_app (pex_ident st_id) args in
    ps_assign __st st
  in
  [ 
    send locals interfaces s_and_t.msg_expr;
    transition locals s_and_t.state_expr;
  ]
  
(*****************************************************************************)
  
(* ideal functionality module ************************************************)

(* vars **********************************************************************)
let var__self = dl (Pst_var ([dl __self], addr_pty))
let var__adv = dl (Pst_var ([dl __adv], addr_pty))
let var__st = dl (Pst_var ([dl __st], named_pty state_type_name))
(*****************************************************************************)

(* proc init *****************************************************************)
let pinit_decl = {
  pfd_name     = dl _init;
  pfd_tyargs   = Fparams_exp [
    (dl _self_, addr_pty);
    (dl _adv_ , addr_pty)
  ];
  pfd_tyresult = unit_pty;
  pfd_uses     = (true, None);
}

let init_name (states : state_tyd IdMap.t) : string =
  let init_state = IdMap.filter (fun _ s -> (ul s).is_initial) states in
  fst (IdMap.choose init_state)

let pinit_body (states : state_tyd IdMap.t) = {
  pfb_locals = [];
  pfb_body   = [
    ps_assign_id __self _self_;
    ps_assign_id __adv _adv_;
    ps_assign_id __st (state_name (init_name states));
  ];
  pfb_return = None;
}

let proc_init (states : state_tyd IdMap.t) =
  let body = pinit_body states in
  dl (Pst_fun (pinit_decl, body))
(*****************************************************************************)    

(* proc parties **************************************************************)
let add_pat_vals
  (inter_id_path : string list)
  (msgtyname : string)
  (mb : message_body_tyd)
  (port : psymbol option)
  (pat_args : pat list option) 
  (locals : locals) : locals =
  let pex_projq_x fieldname = 
    pex_projq (pex_ident __x) (inter_id_path,fieldname) 
  in
  let add_val (valname : string) (subst_expr : pexpr) (locals : locals) : locals =
    { vals = IdMap.add valname subst_expr locals.vals }
  in
  let locals =
    begin match port with
    | None -> locals
    | Some psymbol ->
      let fieldname = name_record_dir_port msgtyname mb in
      let sourceport = pex_projq_x fieldname in
      add_val (ul psymbol) sourceport locals
    end in
  match pat_args with
  | None -> locals
  | Some patl -> 
    List.fold_left2
      (fun locals pat_arg memname ->
        match pat_arg with
        | PatWildcard _ -> locals
        | PatId psymbol ->
          let fieldname = name_record msgtyname memname in
          let memex = pex_projq_x fieldname in
          add_val (ul psymbol) memex locals
      )
      locals patl (fst (List.split (params_map_to_list mb.params_map)))
    
let rec mmcl2matchinstr 
  (locals : locals)
  (interfaces : interfaces) 
  (mmcl : msg_match_clause_tyd list)
  : pstmt =
  match mmcl with
  | [] -> []
  | mmc :: mmcl' ->
    let mpp = ul mmc.msg_pat.msg_path_pat in
    let msgtyname = 
      match mpp.msg_or_star with
      | MsgOrStarMsg n -> n
      | MsgOrStarStar -> failure "impossible, we checked it is not star!" in
    let iip = uc_inter_path mpp.inter_id_path in
    let epdp_path = (iip, name_epdp_op msgtyname) in
    let decmsg = pex_app 
      (pex_proj (dl (PEident (dl (epdp_path), None))) _dec)
      [pex_ident __m] in
    let mb = get_message_body interfaces iip msgtyname in
    let locals' = add_pat_vals iip msgtyname mb mmc.msg_pat.port_id mmc.msg_pat.pat_args locals in
    let stmt = uc_inst_list2ec_stmt locals' interfaces mmc.code in
    let somebr = (PPApp ((pqs "Some", None), [dl(Some (dl __x))]), stmt) in
    let recur = mmcl2matchinstr locals interfaces mmcl' in
    let nonebr = (PPApp ((pqs "None", None), []), recur) in
    [ps_match decmsg [somebr; nonebr]]

let state2matchbranch 
  (locals : locals)
  (interfaces : interfaces)
  (stname, state : string * state_tyd) 
  : ppattern * pstmt =
  let state = ul state in
  let ppat = PPApp (
    (pqs (state_name stname), None),
    List.map (fun (n, _) -> dl (Some (dl n))) (params_map_to_list state.params)
  ) in
  let pstm = mmcl2matchinstr locals interfaces (List.filter 
      (fun mmc -> not (msg_path_pat_ends_star mmc.msg_pat.msg_path_pat)) 
    state.mmclauses) in
  (ppat, pstm)

let party_match 
  (interfaces : interfaces)
  (states : state_tyd IdMap.t) : pinstr = 
  let mtch_ex = pex_ident __st in
  let locals = { vals = IdMap.empty } in
  let branches = List.map (state2matchbranch locals interfaces) (IdMap.bindings states) in
  ps_match mtch_ex branches

let pparties_decl = {
  pfd_name     = dl _parties;
  pfd_tyargs   = Fparams_exp [(dl __m, msg_pty)];
  pfd_tyresult = option_of_pty msg_pty;
  pfd_uses     = (true, None);
}

let pparties_body  
  (interfaces : interfaces)
  (states : state_tyd IdMap.t) =
  let assign__r = ps_assign __r pex_None in
  let party_match = party_match interfaces states in
  {
    pfb_locals = [
    { 
      pfl_names = dl (`Single, [dl __r]);
      pfl_type  = Some (option_of_pty msg_pty);
      pfl_init  = None
    }];(*TODO add all state variables here, with unique names*)
    pfb_body   = [assign__r; party_match];
    pfb_return = Some (pex_ident __r);
  }

let proc_parties
  (interfaces : interfaces)
  (states : state_tyd IdMap.t) =
  let body = pparties_body interfaces states in
  dl (Pst_fun (pparties_decl, body))
(*****************************************************************************)

(* proc invoke ***************************************************************) 
let pinvoke_decl : pfunction_decl = {
  pfd_name     = dl _invoke;
  pfd_tyargs   = Fparams_exp [(dl _m, msg_pty)];
  pfd_tyresult = option_of_pty msg_pty;
  pfd_uses     = (true, None);
}

let call_parties = dl (PScall (
    Some (dl (PLvSymbol (pqs _r))),
    dl ([], dl _parties),
    dl [pex_m]   ))
    
let adv_msg_guard (piex : pexpr) : pexpr =
  pex_tuple [ pex_And [
    pex_app pex_Eq [
      pex_proji  (pex_m) 0;
      pex_Adv
    ];
    pex_app pex_Eq [
      pex_proji (pex_proji  (pex_m) 1) 0;
      pex__self
    ];
    pex_app pex_Eq [
      pex_proji (pex_proji  (pex_m) 1) 1;
      piex
    ];
    pex_app pex_Eq [
      pex_proji (pex_proji  (pex_m) 2) 0;
      pex__adv
    ];
  ]]
    
let pinvoke_body (guard : pexpr) : pfunction_body = 
{
  pfb_locals = [
  { 
    pfl_names = dl (`Single, [dl _r]);
    pfl_type  = Some (option_of_pty msg_pty);
    pfl_init  = Some pex_None
  }];
  pfb_body   = [ps_if_then guard [call_parties]];
  pfb_return = Some (pex_ident _r);
}

let basic_piex (bi_name : string) : pexpr =
print_string ("\n"^bi_name^"\n");
  dl (PEident (dl ([bi_name],opname_pi), None))
  
let comp_piex (di_name : string) (di_mem : string) : pexpr =
print_string ("\n"^di_name^"."^di_mem^"\n");
  dl (PEident (dl ([di_name; di_mem],opname_pi), None))
  
let dir_msg_guard (piex : pexpr) : pexpr =
  pex_tuple [ pex_And [
    pex_app pex_Eq [
      pex_proji  (pex_m) 0;
      pex_Dir
    ];
    pex_app pex_Eq [
      pex_proji (pex_proji  (pex_m) 1) 0;
      pex__self
    ];
    pex_app pex_Eq [
      pex_proji (pex_proji  (pex_m) 1) 1;
      piex
    ];
    pex_app_envport (pex_proji (pex_m) 2);
  ]]

let proc_invoke 
  (di_name : string) 
  (di_mem_names : string list) 
  (ai_name : string) =
  let dir_guards = List.map (fun n -> dir_msg_guard (comp_piex di_name n)) 
    di_mem_names in
  let adv_guard = adv_msg_guard (basic_piex ai_name) in
  let guard = pex_Or (dir_guards@[adv_guard]) in
  let body = pinvoke_body guard in
  dl (Pst_fun (pinvoke_decl, body))
(*****************************************************************************)

let ideal_module 
  (name : string) 
  (fbi : ideal_fun_body_tyd)   
  (interfaces : interfaces) : pmodule_def_or_decl 
  =
  let di_mem_names = fst (List.split (IdMap.bindings interfaces.di)) in
  let items = [
    var__self;
    var__adv;
    var__st;
    proc_init fbi.states;
    proc_parties interfaces fbi.states;
    proc_invoke interfaces.di_name di_mem_names interfaces.ai_name;
  ] in
  let pmodule_def = pmodule_def name items in
  pmodule pmodule_def
  
let write_ideal_fun 
  (ppf : Format.formatter) 
  (name : string) 
  (fbi : ideal_fun_body_tyd)
  (di_name : string)
  (di : basic_inter_body_tyd IdMap.t)
  (ai_name : string) 
  (ai : basic_inter_body_tyd) : unit 
  =
  write_open_theory ppf _UC__IF;
  write_type ppf (state_type fbi.states);
  let interfaces = {
    di_name = uc_name di_name;
    di      = di;
    ai_name = uc_name ai_name;
    ai      = ai
  } in
  let name = uc_name name in
  write_module ppf name (ideal_module name fbi interfaces);
  write_close_theory ppf _UC__IF
(*****************************************************************************)

let clone (tc : theory_cloning) : unit =
  UcEcInterface.process (GthClone tc)

let decl_clone (name : string) (bi : string) (pindx : int): unit =
  let thov = PTHO_Op (`BySyntax {
    opov_nosmt  = false; 
    opov_tyvars = None; opov_args = [];
    opov_retty  = dl PTunivar;
    opov_body   = pex_of_int pindx
    }, `Alias) in
  let cl = {
    pthc_base   = pqs bi;
    pthc_name   = Some (dl name);
    pthc_ext    = [(pqs opname_pi, thov)];
    pthc_prf    = [{pthp_mode = `All (None, []); pthp_tactic = None}];
    pthc_rnm    = [];
    pthc_opts   = [];
    pthc_clears = [];
    pthc_local  = `Global;
    pthc_import = None;
  } in
  clone cl
  
let write_clone (ppf : Format.formatter) (name : string) (bi : string) (pindx : int) : unit =
  decl_clone name bi pindx;
  Format.fprintf stf "@[clone %s as %s with@.  op pi = %i@.proof *.@]@." bi name pindx; (*REMOVE*)
  Format.fprintf ppf "@[clone %s as %s with@.  op pi = %i@.proof *.@]@." bi name pindx;
  print_newline ppf
  
let write_com_int (ppf : Format.formatter) (isdirect : bool) (name : string) (nt : string IdMap.t) : unit =
  let name = uc_name name in
  write_open_theory ppf name;
  let nt = IdMap.to_seq nt in
  let i = if isdirect then ref 1 else ref 2 in
  Seq.iter (fun (n,t) -> write_clone ppf n (uc_name t) !i; i:=!i+2) nt;
  write_close_theory ppf name

type singlefile_typed_spec = {
  dir_inter_map : inter_tyd IdMap.t;
  adv_inter_map : inter_tyd IdMap.t;
  fun_map       : fun_tyd IdMap.t;
  sim_map       : sim_tyd IdMap.t
}

let write_require_import_UCBasicTypes (ppf : Format.formatter) : unit =
  let threq = 
    (None,
     [(dl "UCBasicTypes", None)], (*FIX*)
     Some `Import) in
  UcEcInterface.process (GthRequire threq);
  Format.fprintf stf "@[require import UCBasicTypes.@]@."; (*REMOVE*)
  Format.fprintf ppf "@[require import UCBasicTypes.@]@.";
  print_newline ppf;
  UcEcInterface.process (Gprint (Pr_any (dl(qs "UCBasicTypes")))) (*REMOVE*)
  
let write_op_adv_if_pi (ppf : Format.formatter) : unit =
  write_operator ppf (abs_oper_int opname_adv_if_pi)

let write_ax_adv_if_pi_gt0 (ppf : Format.formatter) : unit =
  decl_axiom (axiom_adv_if_pi_gt0);
  print_axiom ppf axname_adv_if_pi_gt0;
  print_newline ppf
  
let write_file (ppf : Format.formatter) (sts : singlefile_typed_spec) : unit =
  let basfilt i = 
    let ibt = ul i in
    match ibt with
    | BasicTyd  b -> Some b
    | _ -> None
  in

  let compfilt i = 
    let ibt = ul i in
    match ibt with
    | CompositeTyd c -> Some c
    | _ -> None
  in
  
  let idealfilt f =
    let fbt = ul f in
    match fbt with
    | FunBodyIdealTyd fbi -> Some fbi
    | _ -> None
  in
    
  let ideal_funs = filter_map idealfilt sts.fun_map in
  let aiif_names = IdMap.map (fun fbi -> fbi.id_adv_inter) ideal_funs in
  let aiif_names = snd (List.split (IdMap.bindings aiif_names)) in
  let basdir = filter_map basfilt sts.dir_inter_map in
  let comdir = filter_map compfilt sts.dir_inter_map in
  let basadv = filter_map basfilt sts.adv_inter_map in
  let basadv_ideal = IdMap.filter (fun n _ -> List.mem n aiif_names) basadv in
  let basadv_real = IdMap.filter (fun n _ -> not (List.mem n aiif_names)) basadv in
  let comadv = filter_map compfilt sts.adv_inter_map in
  
  write_require_import_UCBasicTypes ppf;
  write_op_adv_if_pi ppf;
  write_ax_adv_if_pi_gt0 ppf;
  IdMap.iter (fun n i -> write_basic_int ppf true false n i) basdir;
  IdMap.iter (fun n i -> write_com_int ppf true n i) comdir;
  IdMap.iter (fun n i -> write_basic_int ppf false true n i) basadv_ideal;
  IdMap.iter (fun n i -> write_basic_int ppf false false n i) basadv_real;
  IdMap.iter (fun n i -> write_com_int ppf false n i) comadv;
  IdMap.iter (fun n f -> write_ideal_fun ppf n f 
                        f.id_dir_inter
                        (IdMap.map 
                          (fun n -> IdMap.find n basdir)
                          (IdMap.find f.id_dir_inter comdir))
                        f.id_adv_inter
                        (IdMap.find f.id_adv_inter basadv_ideal)) ideal_funs
  

(*---------------------------------------------------------------------------*)

let ec_filename (f : string) : string = "UC__"^f^".eca"

let open_formatter (f : string) : out_channel * Format.formatter =
  let fo = open_out_gen [Open_append; Open_creat] 0o666 f in
  let ppf = Format.formatter_of_out_channel fo in
  (fo,ppf)

let close_formatter ((fo,ppf) : out_channel * Format.formatter) : unit =
  Format.pp_print_flush ppf ();
  close_out fo

let remove_file (fn : string) : unit =
  if Sys.file_exists fn 
  then Sys.remove fn 
  else () 

(*---------------------------------------------------------------------------*)

let fn_list (map : 'a IdPairMap.t) : string list =
    List.map (fun ((fn,_), _) -> fn) (IdPairMap.bindings map)
  
let typed_spec2singlefiles (ts : typed_spec) : singlefile_typed_spec IdMap.t =
  let typed_spec2singlefile (fn : string) (ts : typed_spec) : singlefile_typed_spec =
    let toIdmap = fun (f,n) e idmap -> if (f=fn) then IdMap.add n e idmap else idmap in
    let dm = IdPairMap.fold toIdmap ts.dir_inter_map IdMap.empty in
    let am = IdPairMap.fold toIdmap ts.adv_inter_map IdMap.empty in
    let fm = IdPairMap.fold toIdmap ts.fun_map IdMap.empty in
    let sm = IdPairMap.fold toIdmap ts.sim_map IdMap.empty in
    { dir_inter_map = dm;
      adv_inter_map = am;
      fun_map = fm;
      sim_map = sm }   
  in
  let fns = 
    (fn_list ts.dir_inter_map)@
    (fn_list ts.adv_inter_map)@
    (fn_list ts.fun_map)@
    (fn_list ts.sim_map) in
  let uniq_fns = IdSet.of_list fns in
  IdSet.fold 
    (fun fn idmap -> IdMap.add fn (typed_spec2singlefile fn ts) idmap) 
    uniq_fns IdMap.empty
  
let generate_ec (ts:typed_spec) : unit =
  let stss = typed_spec2singlefiles ts in
  let (fn, sts) = IdMap.min_binding stss in
  let fn = ec_filename fn in
  remove_file fn;
  let (fo,ppf) = open_formatter fn in
  write_file ppf sts;
  close_formatter (fo,ppf)

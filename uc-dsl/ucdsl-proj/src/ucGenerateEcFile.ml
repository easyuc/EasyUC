open UcTypedSpec
open EcParsetree
open UcMessage

let stf = Format.std_formatter (*REMOVE*)

let dl = UcUtils.dummyloc

let qs = qsymb_of_symb

let pqs (name : string) = dl (qs name)

let ul = EcLocation.unloc

let decl_open_theory (name : string) : unit =
  UcEcInterface.process (GthOpen (`Global, false, dl name))
  
let decl_close_theory (name : string) : unit =
  UcEcInterface.process (GthClose ([], dl name))

let decl_operator (pop : poperator) : unit =
  UcEcInterface.process (Goperator pop)
  
let decl_axiom (pax : paxiom) : unit =
  UcEcInterface.process (Gaxiom pax)
  
let decl_type (ptds : ptydecl list) : unit =
  UcEcInterface.process (Gtype ptds)
  
let print_newline (ppf : Format.formatter) : unit =
  Format.fprintf stf "@."; (*REMOVE*)
  Format.fprintf ppf "@."
  
let print_theory (ppf : Format.formatter) (name : string) : unit = 
  let env = UcEcInterface.env () in
  let ppe = EcPrinting.PPEnv.ofenv env in
  let pth = EcEnv.Theory.lookup (qs name) env in
  EcPrinting.pp_theory ppe stf pth; (*REMOVE*)
  EcPrinting.pp_theory ppe ppf pth;
  print_newline ppf

let print_operator (ppf : Format.formatter) (name : string) : unit = 
  let env = UcEcInterface.env () in
  let ppe = EcPrinting.PPEnv.ofenv env in
  let op = EcEnv.Op.lookup (qs name) env in
  EcPrinting.pp_opdecl ppe stf op; (*REMOVE*)
  EcPrinting.pp_opdecl ppe ppf op;
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

let option_of_pty (name : string) = dl (PTapp (pqs "option",[named_pty name]))

let addr_pty = named_pty "addr"

let port_pty = named_pty "port"

let msg_pty = named_pty "msg"

let int_pty = named_pty "int"
  
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

let name_record (msg_name : string) (param_name : string) : string = msg_name^"__"^param_name

let name_record_dir_port (name : string)  (mb : message_body_tyd) : string =
  name_record name (EcUtils.oget mb.port)
 
let params_map_to_list (pm : ty_index IdMap.t) : (string * pty) list =
  let bpm = IdMap.bindings pm in
  let bpm = List.map (fun (s,ti) -> (s, ul ti)) bpm in
  let bpm_ord = List.sort (fun (_,(_,i1)) (_,(_,i2)) -> i1-i2) bpm in
  List.map (fun (name,((_,pty),_)) -> (name, pty)) bpm_ord

let decl_msg_type (name : string) (mb : message_body_tyd) : unit =
  let msg_data = List.map (fun (s,t) -> (dl (name_record name s), t)) 
    (params_map_to_list mb.params_map) in
  let func_addr = (dl (name_record_func name), addr_pty) in
  let dir_port = (dl (name_record_dir_port name mb), port_pty) in
  let body = PTYD_Record (func_addr :: dir_port :: msg_data) in
  let pty = {
    pty_name   = dl name;
    pty_tyvars = [];
    pty_body   = body;
    pty_locality = `Global;
  } in
  decl_type [pty]

let enc_op_name (name : string) : string = "enc_"^name

let pex_ident (name : string) : pexpr = dl (PEident (pqs name, None))

let pex_Dir = pex_ident "Dir"

let pex_Adv = pex_ident "Adv"

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

let rec epdp_pty_univ (t : pty) : pexpr =
  match ul t with
  | PTtuple  ptys -> epdp_tuple_univ ptys
  | PTnamed  pqs  -> let (_, name) = ul pqs in epdp_name_univ name
  | _ -> failure ("Only tuples and named types supported." )
and epdp_tuple_univ (ptys : pty list) : pexpr =
  let epdp_name = epdp_tuple_name (List.length ptys) in
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

let pex_int_0 = dl (PEint EcBigInt.zero)

let decl_enc_op (isdirect : bool) (mty_name : string) (mb : message_body_tyd) : unit =
  let var_name = "x" in
  let u = enc_u var_name mty_name mb.params_map in
  let tag = pex_int_0 in
  let selfport = pex_tuple [
    pex_proj (pex_ident var_name) (name_record_func mty_name); 
    pex_ident opname_pi ] in
  let otherport = pex_proj (pex_ident var_name) (name_record_dir_port mty_name mb) in
  let ptsource = if mb.dir = In then otherport else selfport in
  let ptdest = if mb.dir = In then selfport else otherport in
  let mode = if isdirect then pex_Dir else pex_Adv in
  let encex = pex_tuple [mode; ptsource; ptdest; tag; u] in
  let args = [([dl(Some (dl var_name))], named_pty mty_name) ] in
  let def = PO_concr (msg_pty, encex) in
  let penc =
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
  } in
  decl_operator penc

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

let pex_Or = pex_ident "\\/"

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

let decl_dec_op (isdirect : bool) (mty_name : string) (mb : message_body_tyd) : unit =
  let var_name = "m" in
  let mode = "mod" in
  let pt1 = "pt1" in
  let pt2 = "pt2" in
  let funcport = if mb.dir = In then pt1 else pt2 in
  let otherport = if mb.dir = In then pt2 else pt1 in 
  let tag = "tag" in
  let v = "v" in
  let osym (name : string) = dl (Some (dl name)) in
  let pat = dl (LPTuple [osym mode; osym pt1; osym pt2; osym tag; osym v]) in
  
  let wty = (pex_ident var_name, None) in
  
  let notmode = if isdirect then pex_Adv else pex_Dir in
  let if1 = pex_app pex_Eq [pex_ident mode; notmode] in
  let no1 = pex_app pex_Eq [pex_proji (pex_ident pt1) 1; pex_ident opname_pi] in
  let no2 = pex_app pex_Eq [pex_ident tag; pex_int_0] in
  let if2 = pex_app pex_Or [pex_app pex_Not [no1]; pex_app pex_Not [no2]] in
  let if_cond = pex_tuple [pex_app pex_Or [if1; if2]] in
  
  let p = "p" in
  let n' (pn : string) : string = pn^"'" in
  let pns = fst (List.split (params_map_to_list mb.params_map)) in
  let patm = dl (LPTuple (List.map (fun pn -> osym (n' pn)) pns)) in
  let wtym = (pex_ident p, None) in
  let funcfld = pexrfield (name_record_func mty_name) (pex_proji (pex_ident funcport) 0) in
  let pt1fld = pexrfield (name_record_dir_port mty_name mb) (pex_ident otherport) in
  let dataflds = List.map 
    (fun pn -> pexrfield (name_record mty_name pn) (pex_ident (n' pn)) ) 
    pns in
  let msg = pex_record None (funcfld::pt1fld::dataflds) in
  let omsg = pex_app pex_Some [msg] in

  let ex2 = 
    if pns = [] 
    then omsg
    else pex_let patm wtym omsg  in
  let pat2 = PPApp ((pqs "Some", None), [dl(Some (dl p))]) in
  let mtch2 = (pat2, ex2) in

  let pat1 = PPApp ((pqs "None", None), []) in
  let mtch1 = (pat1, pex_None) in

  let dd = pex_proj (epdp_data_univ mb.params_map) "dec" in
  let pmex = pex_app dd [pex_ident v] in
  let else_br = pex_match pmex [mtch1; mtch2] in

  let pif = pex_if if_cond pex_None else_br in
  
  let decex = pex_let pat wty pif in
  let args = [([dl(Some (dl var_name))], msg_pty) ] in
  let ret_pty = option_of_pty mty_name in

  let def = PO_concr (ret_pty, decex) in
  let pdec =
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
  } in
  decl_operator pdec

let name_epdp_op (mty_name : string) : string = "epdp_"^mty_name

let decl_epdp_op (mty_name : string) : unit =
  let enc = pexrfield "enc" (pex_ident (enc_op_name mty_name)) in
  let dec = pexrfield "dec" (pex_ident (dec_op_name mty_name)) in
  let epdp = pex_record None [enc; dec] in
  let def = PO_concr (dl PTunivar, epdp) in
  let pepdp =
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
  } in
  decl_operator pepdp

let name_lemma_epdp_valid (name : string) : string =
  "valid_epdp_"^name

let decl_lemma_epdp (name : string) : unit =
  let f_ve = pform_ident "valid_epdp" in
  let f_e = pform_ident (name_epdp_op name) in
  let pfrm = dl (PFapp (f_ve, [f_e])) in 
  let lem =
  {
    pa_name     = dl (name_lemma_epdp_valid name);
    pa_tyvars   = None;
    pa_vars     = None;
    pa_formula  = pfrm;
    pa_kind     = PLemma None;
    pa_nosmt    = false;
    pa_locality = `Global;
  } in
  decl_axiom lem

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
  
let hint_simplify_epdp (name : string) : unit =
  UcEcInterface.process (Greduction 
    ([`EqTrue], [([pqs (name_lemma_epdp_valid name)], None)]))

let hint_rewrite_epdp (name : string) : unit =
  UcEcInterface.process (Gaddrw
    (`Global, pqs "epdp", [pqs (name_lemma_epdp_valid name)]))

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
  | _ -> failure ("Only tuples and named types supported." )
and epdp_tuple_univ_form (ptys : pty list) : pformula =
  let epdp_name = epdp_tuple_name (List.length ptys) in
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

let decl_lemma_eq_of_valid (isdirect : bool) (mty_name : string) (mb : message_body_tyd) : unit =
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
  let fmode = if isdirect then pform_Dir else pform_Adv in
  let fsadd = dl (PFproj (fx, pqs (name_record_func mty_name))) in
  let funcport = dl (PFtuple [fsadd; pform_ident opname_pi]) in
  let otherport = dl (PFproj (fx, pqs (name_record_dir_port mty_name mb))) in
  let fdport = if mb.dir = In then funcport else otherport in
  let fsport = if mb.dir = In then otherport else funcport in
  let fdata = enc_u_form x mty_name mb.params_map in
  let fmsg = dl (PFtuple [fmode; fdport; fsport; pf_0; fdata] ) in
  
  let flet = dl (PFlet (dl (LPSymbol (dl "x")), (foget, None), fmsg)) in
  let f_r = pform_app f_eq [fm; flet] in
  let f_imp = pform_ident "=>" in
  let pfrm = pform_app f_imp [f_l; f_r] in 
  
  let lem =
  {
    pa_name     = dl (name_lemma_eq_of_valid mty_name);
    pa_tyvars   = None;
    pa_vars     = vars;
    pa_formula  = pfrm;
    pa_kind     = PLemma None;
    pa_nosmt    = false;
    pa_locality = `Global;
  } in
  decl_axiom lem

let decl_message (isdirect : bool) (name : string) (mb : message_body_tyd) : unit =
  decl_msg_type name mb;
  decl_enc_op isdirect name mb;
  decl_dec_op isdirect name mb;
  decl_epdp_op name;
  decl_lemma_epdp name;
  proof_admit_qed ();
  hint_simplify_epdp name;
  hint_rewrite_epdp name;
  decl_lemma_eq_of_valid isdirect name mb;
  proof_admit_qed ()
  
let write_basic_int (ppf : Format.formatter) (isdirect : bool) (name : string) (bibt : basic_inter_body_tyd) : unit =
  decl_open_theory name;
  decl_operator pi_op;
  IdMap.iter (fun n mb -> decl_message isdirect n mb) bibt;
  decl_close_theory name;
  print_theory ppf name (*TODO print theory part by part*)
  
let write_basic_inter (ppf : Format.formatter) (isdirect : bool) (name : string) (dir_int : inter_tyd) : unit =
  let ibt = ul dir_int in
  match ibt with
  | BasicTyd  b -> write_basic_int ppf isdirect name b
  | _ -> ()

let clone (tc : theory_cloning) : unit =
  UcEcInterface.process (GthClone tc)

let pex_of_int (i : int) : pexpr =
  dl (PEint (EcBigInt.of_int i))

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
  Format.fprintf stf "@.@[clone %s as %s with@.  op pi = %i@.proof *.@]@." bi name pindx; (*REMOVE*)
  Format.fprintf ppf "@.@[clone %s as %s with@.  op pi = %i@.proof *.@]@." bi name pindx

let write_open_theory (ppf : Format.formatter) (name : string) : unit =
  decl_open_theory name;
  Format.fprintf stf "@.@[theory %s.@]@." name; (*REMOVE*)
  Format.fprintf ppf "@.@[theory %s.@]@." name
  
let write_close_theory (ppf : Format.formatter) (name : string) : unit =
  decl_close_theory name;
  Format.fprintf stf "@.@[end %s.@]@." name; (*REMOVE*)
  Format.fprintf ppf "@.@[end %s.@]@." name
  
let write_com_int (ppf : Format.formatter) (isdirect : bool) (name : string) (nt : string IdMap.t) : unit =
  write_open_theory ppf name;
  let nt = IdMap.to_seq nt in
  let i = if isdirect then ref 1 else ref 2 in
  Seq.iter (fun (n,t) -> write_clone ppf n t !i; i:=!i+2) nt;
  write_close_theory ppf name
  
let write_composite_inter (ppf : Format.formatter) (isdirect : bool) (name : string) (dir_int : inter_tyd) : unit =
  let ibt = ul dir_int in
  match ibt with
  | CompositeTyd c -> write_com_int ppf isdirect name c
  | _ -> ()

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
  UcEcInterface.process (Gprint (Pr_any (dl(qs "UCBasicTypes")))) (*REMOVE*)
  
let write_op_adv_if_pi (ppf : Format.formatter) : unit =
  decl_operator (abs_oper_int opname_adv_if_pi);
  print_operator ppf opname_adv_if_pi

let write_ax_adv_if_pi_gt0 (ppf : Format.formatter) : unit =
  decl_axiom (axiom_adv_if_pi_gt0);
  print_axiom ppf axname_adv_if_pi_gt0
  
let write_file (ppf : Format.formatter) (sts : singlefile_typed_spec) : unit =
  write_require_import_UCBasicTypes ppf;
  write_op_adv_if_pi ppf;
  write_ax_adv_if_pi_gt0 ppf;
  IdMap.iter (fun n d -> write_basic_inter     ppf true n d) sts.dir_inter_map;
  IdMap.iter (fun n d -> write_composite_inter ppf true n d) sts.dir_inter_map
  

(*---------------------------------------------------------------------------*)

let ec_filename (f : string) : string = f^".eca"

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
  

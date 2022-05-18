open EcParsetree
open UcSpecTypedSpecCommon
open UcTypedSpec
open UcMessage
open UcGenEcInterface
open UcGenCore
  
(* construction of message theory ********************************************)

(* message type declaration *) 
let msg_type (sh : shadowed) (name : string) (mb : message_body_tyd) : ptydecl =
  let msg_data = List.map (fun (s,t) -> (dl (name_record name s), (qualify_ty sh t)))
    (params_map_to_list mb.params_map) in
  let self_addr = (dl (name_record_func name), (qualify_ty sh addr_pty)) in
  let other_port =
    if (isdirect mb)
    then (dl (name_record_dir_port name mb), (qualify_ty sh port_pty))
    else (dl (name_record_adv name), (qualify_ty sh addr_pty)) in
  record_decl name (self_addr :: other_port :: msg_data)
  
(* enc op *) 
let enc_op_name (name : string) : string = "enc_"^name

let enc_op (ppf : Format.formatter) (sh : shadowed) 
(tag : int) (mty_name : string) (mb : message_body_tyd) : shadowed * poperator =
  let var_name = "x" in
  let sh, u = enc_u (Some ppf) sh var_name mty_name mb.params_map in
  let selfport = pex_tuple [
    pex_proj (pex_ident var_name) (name_record_func mty_name); 
    pex_ident _pi ] in
  let isdirect = isdirect mb in
  let otherport = 
    if isdirect
    then pex_proj (pex_ident var_name) (name_record_dir_port mty_name mb) 
    else pex_tuple [
      pex_proj (pex_ident var_name) (name_record_adv mty_name); 
      pex_ident __adv_if_pi ]
    in
  let ptsource = if mb.dir = In then otherport else selfport in
  let ptdest = if mb.dir = In then selfport else otherport in
  let mode = if isdirect then pex_Dir else pex_Adv in
  let encex = pex_tuple [mode; ptdest; ptsource; pex_of_int tag; u] in
  let args = [(var_name, named_pty mty_name)] in
  sh, op_of_argstyex (enc_op_name mty_name) args (qualify_ty sh msg_pty) encex

(* dec operator *)
let dec_op_name (name : string) : string = "dec_"^name

let dec_op (sh : shadowed) (tag : int) (mty_name : string) (mb : message_body_tyd) : poperator =
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
    [pex_app pex_Eq [pex_proji (pex_ident otherport) 1; pex_ident __adv_if_pi]] in
  let no1 = pex_app pex_Not 
    [pex_app pex_Eq [pex_proji (pex_ident funcport) 1; pex_ident _pi]] in
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
    then ppatSome_
    else ppatSome p in
  let mtch2 = (pat2, ex2) in
  let mtch1 = (ppatNone, pex_None) in

  let _ , epdp_op = epdp_data_univ None sh pex_pqident pex_app mb.params_map in
  let dd = pex_proj epdp_op "dec" in
  let pmex = pex_app dd [pex_ident v] in
  let else_br = pex_match pmex [mtch1; mtch2] in

  let pif = pex_if if_cond pex_None else_br in
  
  let decex = pex_let pat wty pif in
  let args = [(var_name, qualify_ty sh msg_pty) ] in
  let ret_pty = option_of_msgty sh mty_name in
  op_of_argstyex (dec_op_name mty_name) args ret_pty decex

(* epdp operator for message type *)

let epdp_op (mty_name : string) : poperator =
  let enc = pexrfield "enc" (pex_ident (enc_op_name mty_name)) in
  let dec = pexrfield "dec" (pex_ident (dec_op_name mty_name)) in
  let epdp = pex_record None [enc; dec] in
  op_of_ex (name_epdp_op mty_name) epdp

(* lemma eq_of_valid_msgtyname *)
let name_lemma_eq_of_valid (name : string) : string =
  "eq_of_valid_"^name

let lemma_eq_of_valid (sh : shadowed) (tag : int) (mty_name : string) (mb : message_body_tyd) : paxiom =
  let m = "m" in
  let vars = [(m, qualify_ty sh msg_pty)] in
  
  let fepdp = pform_ident (name_epdp_op mty_name) in
  let fm = pform_ident m in
  let f_l = pform_app (pform_ident "is_valid") [fepdp; fm] in
  let f_eq = pform_ident "=" in
  let fdec = pform_tuple [pform_app (pform_proj fepdp _dec) [fm]] in 
  let foget = pform_app (pform_ident "oget") [fdec] in
  
  let x = "x" in
  let fx = pform_ident x in
  let isdirect = isdirect mb in
  let fmode = if isdirect then pform_Dir else pform_Adv in
  let fsadd = pform_proj fx (name_record_func mty_name) in
  let funcport = pform_tuple [fsadd; pform_ident _pi] in
  let otherport = 
    if isdirect
    then pform_proj fx (name_record_dir_port mty_name mb)
    else let fsadv = pform_proj fx (name_record_adv mty_name) in
      pform_tuple [fsadv; pform_ident __adv_if_pi]
    in
  let fdport = if mb.dir = In then funcport else otherport in
  let fsport = if mb.dir = In then otherport else funcport in
  let fdata = enc_u_form sh x mty_name mb.params_map in
  let fmsg = pform_tuple [fmode; fdport; fsport; pf_of_int tag; fdata] in
  
  let flet = dl (PFlet (dl (LPSymbol (dl "x")), (foget, None), fmsg)) in
  let f_r = pform_app f_eq [fm; flet] in
  let f_imp = pform_ident "=>" in
  let pfrm = pform_app f_imp [f_l; f_r] in
  paxiom_lemma_vars (name_lemma_eq_of_valid mty_name) vars pfrm

let write_message (ppf : Format.formatter) (sh : shadowed) 
  (tag : int) (name : string) (mb : message_body_tyd) : shadowed =
  write_type ppf (msg_type sh name mb);
  let sh, op = enc_op ppf sh tag name mb in
  write_operator ppf op;
  write_operator ppf (dec_op sh tag name mb);
  let epdpop = epdp_op name in
  write_operator ppf epdpop;
  let epdplem = lemma_epdp (ul epdpop.po_name) in
  write_lemma ppf epdplem;
  let lename = ul epdplem.pa_name in
  write_hint_simplify ppf lename;
  write_hint_rewrite ppf _epdp lename;
  write_lemma ppf (lemma_eq_of_valid sh tag name mb);
  sh
  
(* basic interface *) 
let pi_op : poperator = abs_oper_int _pi
  
let pi_op2 = oper_int _pi 2

let add_shadowing_decls (sh : shadowed) (name : string) : shadowed =
  let sh = add_ty_name sh name in
  let sh = add_op_name sh (name_epdp_op name) in
  sh
  
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
  let _ = List.fold_left ( fun (i,sh) (n, mb) -> 
    let sh = add_shadowing_decls sh n in
    let sh = write_message ppf sh i n mb in
    (i+1, sh)
  ) (0,init_shadowed) bibtl in
  write_close_theory ppf name

(*****************************************************************************)

(* ideal functionality theory ************************************************)

(* constructing state type *)
let state_type_name = "_state"

let state_type (states : state_tyd IdMap.t) : ptydecl =
  let s2e (sname, sbod : string * state_tyd) : (psymbol * pty list) =
    let sptys = snd (List.split (params_map_to_list (ul sbod).params)) in
    (dl (state_name sname), sptys)
  in
  let ste = List.map s2e (IdMap.bindings states) in
  datatype_decl state_type_name ste



(* vars *)
let var__self = dl (Pst_var ([dl __self], addr_pty))
let var__adv = dl (Pst_var ([dl __adv], addr_pty))
let var__st = dl (Pst_var ([dl __st], named_pty state_type_name))

(* proc init *)
let pinit_decl = pfunction_decl 
  _init
  [
    (dl _self_, addr_pty);
    (dl _adv_ , addr_pty)
  ]
  unit_pty


let init_name (states : state_tyd IdMap.t) : string =
  let init_state = IdMap.filter (fun _ s -> (ul s).is_initial) states in
  fst (IdMap.choose init_state)

let pinit_body (states : state_tyd IdMap.t) = pfunction_body
  []
  [
    ps_assign_id __self _self_;
    ps_assign_id __adv _adv_;
    ps_assign_id __st (state_name (init_name states));
  ]
  None

let proc_init (states : state_tyd IdMap.t) =
  fun_def pinit_decl (pinit_body states)

(* proc state *)

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
      (pex_proj (pex_pqident (dl (epdp_path))) _dec)
      [pex_ident __m] in
    let mb = get_message_body interfaces iip msgtyname in
    let locals = { vals = IdMap.empty } in
    let locals' = add_pat_vals iip msgtyname mb mmc.msg_pat.port_id mmc.msg_pat.pat_args locals in
    let stmt = uc_inst_list2ec_stmt locals' interfaces mmc.code in
    let somebr = (ppatSome __x, stmt) in
    let recur = mmcl2matchinstr interfaces mmcl' in
    let nonebr = (ppatNone, recur) in
    [ps_match decmsg [somebr; nonebr]]

let proc_state_name (stname : string) : string = "proc"^stname

let proc_state_decl (stname : string) (state : state_body_tyd) : pfunction_decl = 
  let pl = params_map_to_list state.params in
  let params = List.map (fun (name, pty) -> (dl name,pty)) pl in
  pfunction_decl
    (proc_state_name stname)
    ((dl __m, msg_pty)::params)
    (option_of_pty msg_pty)

let get_vars (state : state_body_tyd) : pfunction_local list =
    let vars = params_map_to_list state.vars in
    List.map (fun (n,t) -> pf_var n t) vars

let proc_state_body (interfaces : interfaces) (state : state_body_tyd) =
  let assign__r = ps_assign __r pex_None in
  let state_match = mmcl2matchinstr interfaces (List.filter 
      (fun mmc -> not (msg_path_pat_ends_star mmc.msg_pat.msg_path_pat)) 
    state.mmclauses) in
    pfunction_body
      ((get_vars state)@[pf_var __r  (option_of_pty msg_pty)])
      (assign__r :: state_match)
      (Some (pex_ident __r))

let proc_state (interfaces : interfaces) (stname, state : string * state_tyd) =
  let state = ul state in
  let pdecl = proc_state_decl stname state in
  let pbody = proc_state_body interfaces state in
  fun_def pdecl pbody
(*****************************************************************************)

(* proc parties **************************************************************)
let call_state stname param_names =
    let param_exl = List.map (fun n -> pex_ident n) param_names in
    ps_call __r (proc_state_name stname) (pex_ident __m::param_exl)

let state2matchbranch
  (stname, state : string * state_tyd) 
  : ppattern * pstmt =
  let state = ul state in
  let param_names = fst (List.split (params_map_to_list state.params)) in
  let ppat = ppattern (state_name stname) 
    (List.map (fun n -> Some  n) param_names) in
  let pstmt = [call_state stname param_names] in
  (ppat, pstmt)

let party_match
  (states : state_tyd IdMap.t) : pinstr = 
  let mtch_ex = pex_ident __st in
  let branches = List.map state2matchbranch (IdMap.bindings states) in
  ps_match mtch_ex branches

let pparties_decl : pfunction_decl = pfunction_decl
  _parties
  [(dl __m, msg_pty)]
  (option_of_pty msg_pty)

let pparties_body
  (states : state_tyd IdMap.t) =
  let party_match = party_match states in
  pfunction_body
    [pf_var __r  (option_of_pty msg_pty)]
    [party_match]
    (Some (pex_ident __r))

let proc_parties
  (states : state_tyd IdMap.t) =
  fun_def pparties_decl (pparties_body states)
(*****************************************************************************)

(* proc invoke ***************************************************************) 
let pinvoke_decl : pfunction_decl = pfunction_decl
  _invoke
  [(dl _m, msg_pty)]
  (option_of_pty msg_pty)

let call_parties = ps_call _r _parties [pex_m]
    
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
    
let pinvoke_body (guard : pexpr) : pfunction_body = pfunction_body
  [pf_var _r (option_of_pty msg_pty)]
  [ps_if_then guard [call_parties]]
  (Some (pex_ident _r))

let basic_piex (bi_name : string) : pexpr =
  pex_pqident (dl ([bi_name],_pi))
  
let comp_piex (di_name : string) (di_mem : string) : pexpr =
  pex_pqident (dl ([di_name; di_mem],_pi))
  
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
  fun_def pinvoke_decl body
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
  ]@
  (List.map (proc_state interfaces) (IdMap.bindings fbi.states))@ 
  [
    proc_parties fbi.states;
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
  
let write_clone (ppf : Format.formatter)
(name : string) (base : string) (pindx : int ) : unit =
  clone (theory_cloning name base _pi (pex_of_int pindx));
  Format.fprintf stf "@[clone %s as %s with@.  op pi = %i@.proof *.@]@." base name pindx; (*REMOVE*)
  Format.fprintf ppf "@[clone %s as %s with@.  op pi = %i@.proof *.@]@." base name pindx;
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
  
let axiom_adv_if_pi_gt0 : paxiom =
  let f_le = pform_ident "<" in
  let f_ax = pform_ident __adv_if_pi in 
  let pfrm = pform_app f_le [pf_0; f_ax] in
  paxiom_axiom __adv_if_pi_gt0 pfrm

let write_ax_adv_if_pi_gt0 (ppf : Format.formatter) : unit =
  decl_axiom (axiom_adv_if_pi_gt0);
  print_axiom ppf __adv_if_pi_gt0;
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
  
  write_require_import ppf _UCBasicTypes;
  write_operator ppf (abs_oper_int __adv_if_pi);
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

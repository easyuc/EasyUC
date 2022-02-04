open UcTypedSpec
open EcLocation
open EcSymbols
open UcMessage
module EI = EcInductive

(* messy *)

let fileMap (x : 'a IdPairMap.t) : ('a IdMap.t) IdMap.t =
  IdPairMap.fold 
    (fun (f,s) a fm -> if (IdMap.mem f fm)
      then IdMap.add f (IdMap.add s a (IdMap.find f fm)) fm   
      else IdMap.add f (IdMap.singleton s a) fm
    ) 
    x IdMap.empty 

let pp_tydecl ppf ptd =
  let env = UcEcInterface.env () in
  let ppe = EcPrinting.PPEnv.ofenv env in
  EcPrinting.pp_typedecl ppe Format.std_formatter ptd;
  EcPrinting.pp_typedecl ppe ppf ptd
  
let pp_theory ppf pth =
  let env = UcEcInterface.env () in
  let ppe = EcPrinting.PPEnv.ofenv env in
  EcPrinting.pp_theory ppe Format.std_formatter pth;
  EcPrinting.pp_theory ppe ppf pth
  
(*let pqname_of_string (id:string) =
  let env = UcEcInterface.env () in
  EcPath.pqname (EcEnv.root env) id*)
let path_of_string (id:string) : EcPath.path =
  EcPath.fromqsymbol ([],id)
  
let locality0 : EcTypes.locality = `Global
(*using ecScope.add_record as a starting point and copying parts of code from
ecScope.add_record, ecHiInductive.trans_record 
*)  
let ec_tydecl_from_msg (id:string) (mb:message_body_tyd) : EcPath.path * EcDecl.tydecl =
  let tpath = path_of_string id in
  let fields = IdMap.bindings 
    (IdMap.map (fun til -> let ty,_ = unloc til in ty) mb.params_map) in
  let record = 
    { EI.rc_path = tpath; EI.rc_tparams = []; EI.rc_fields = fields; } in
  let scheme  = EI.indsc_of_record record in
  tpath,
  {
    tyd_params = record.EI.rc_tparams;
    tyd_type   = `Record (scheme, record.EI.rc_fields); 
    tyd_loca   = locality0;
    tyd_resolve= true;}

let mk_op0 (ty_params : EcDecl.ty_params) (ty : EcTypes.ty) (opbody : EcDecl.opbody option) : EcDecl.operator =
  EcDecl.mk_op ~opaque:false ty_params ty opbody locality0

let import0 = EcTheory.import0

let th_item0 (item_r : EcTheory.theory_item_r) : EcTheory.theory_item =
  { ti_item   = item_r;
    ti_import = import0; }
    
let op_th_item (id:string) (op:EcDecl.operator) : EcTheory.theory_item =
  th_item0 (EcTheory.Th_operator (id,op))
  
let nullary_int_op =
  mk_op0 [] EcTypes.tint None
 
let op_pi_th_item (id:string) : EcTheory.theory_item =
  op_th_item id nullary_int_op
  
let mk_ty_from_s (s:string) : EcTypes.ty =
  EcTypes.tconstr (EcPath.psymbol s) []

let msg_ty = mk_ty_from_s "msg"

let enc_op_ty (mt_id : string) =
  EcTypes.tfun (mk_ty_from_s mt_id) msg_ty

let enc_op (mt_id : string) : EcDecl.operator =
  mk_op0 [] (enc_op_ty mt_id) None

let dec_op_ty (mt_id : string) =
  EcTypes.tfun msg_ty (mk_ty_from_s mt_id)
  
let dec_op (mt_id : string) : EcDecl.operator =
  mk_op0 [] (dec_op_ty mt_id) None

let enc_op_name mt_id = "enc_"^mt_id

let dec_op_name mt_id = "dec_"^mt_id

let enc_op_th_item (mt_id:string) : EcTheory.theory_item =
  let op_decl = enc_op mt_id in
  let op_name = enc_op_name mt_id in
  op_th_item op_name op_decl
  
let dec_op_th_item (mt_id:string) : EcTheory.theory_item =
  let op_decl = dec_op mt_id in
  let op_name = dec_op_name mt_id in
  op_th_item op_name op_decl

let enc_dec_typs (mt_id:string) =
  [mk_ty_from_s mt_id; msg_ty]

let epdp_mt_ty (mt_id:string) env =
  let epdp_p , _ = EcEnv.Ty.lookup ([],"epdp") env in
  let tyl = enc_dec_typs mt_id in
  EcTypes.tconstr epdp_p tyl
  
let epdp_ty env =
  let epdp_p , _ = EcEnv.Ty.lookup ([],"epdp") env in
  EcTypes.tconstr epdp_p []
  
let epdp_mt_op_name mt_id =
  "epdp_"^mt_id

let epdp_op_th_item (mt_id:string) : EcTheory.theory_item =
  let env = UcEcInterface.env () in
  
  (*let epdp_p , epdp_tydecl = EcEnv.Ty.lookup ([],"epdp") env in
  print_string (EcPath.tostring epdp_p);
  let epdp_ty = EcEnv.Ty.unfold epdp_p [mk_ty_from_s mt_id; msg_ty] env in
  let epdp_rcrd = match epdp_tydecl with
                | ({ tyd_type = `Record rcrd }) -> rcrd
                | _ -> UcMessage.failure "noooo oooo"
                in 
  let epdp_ty = EcDecl.ty_instanciate epdp_tydecl.tyd_params [mk_ty_from_s mt_id; msg_ty] in
  let epdp_op = EcEnv.Op.by_path epdp_p env in *)
  
  let epdp_mt_ty = epdp_mt_ty mt_id env in
  let mk_epdp_p , _ = EcEnv.Op.lookup ([],"mk_epdp") env in
  let epdp_mt_op_ex = EcTypes.e_op mk_epdp_p (enc_dec_typs mt_id) epdp_mt_ty in
  let enc_mt_op_ex = EcTypes.e_op (path_of_string (enc_op_name mt_id)) [] (enc_op_ty mt_id) in
  let dec_mt_op_ex = EcTypes.e_op (path_of_string (dec_op_name mt_id)) [] (dec_op_ty mt_id) in
  let epdp_mt_ex = EcTypes.e_app  epdp_mt_op_ex [enc_mt_op_ex;dec_mt_op_ex] epdp_mt_ty in
  let epdp_mt_body = EcDecl.OP_Plain (epdp_mt_ex,true) in
  let op_decl = (mk_op0 [] epdp_mt_ty (Some epdp_mt_body)) in
  let op_name = epdp_mt_op_name mt_id in
  op_th_item op_name op_decl
  
let lemma_th_item (name : string) (f:EcCoreFol.form): EcTheory.theory_item =
  th_item0 (EcTheory.Th_axiom
    (name,
    { ax_tparams    = [];
      ax_spec       = f;
      ax_kind       = `Lemma;
      ax_loca       = locality0;
      ax_visibility = `Visible; 
    }))

let valid_epdp_op_p = path_of_string "valid_epdp"
  
let valid_epdp_op_f env : EcCoreFol.form =
  let epdp_ty = epdp_ty env in
  let valid_epdp_op_ty = EcTypes.toarrow [epdp_ty] EcTypes.tbool in
  EcCoreFol.f_op valid_epdp_op_p [] valid_epdp_op_ty

let epdp_mt_op_p mt_id = path_of_string (epdp_mt_op_name mt_id)

let valid_epdp_mt_f (mt_id:string) : EcCoreFol.form =
  let env = UcEcInterface.env () in
  (*let valid_epdp_op_p , _ = EcEnv.Op.lookup ([],"valid_epdp") env in !!! the path is Top.UCEncoding.valid_epdp which gets printed out*)
  let epdp_mt_ty = epdp_mt_ty mt_id env in
  let epdp_mt_op_f = EcCoreFol.f_op (epdp_mt_op_p mt_id) [] epdp_mt_ty in
  EcCoreFol.f_app (valid_epdp_op_f env) [epdp_mt_op_f] EcTypes.tbool

let valid_epdp_mt_lemma_name (mt_id:string) =
  "valid_epdp_"^mt_id
  
let lemma_valid_epdp_th_item (mt_id:string) : EcTheory.theory_item =
  lemma_th_item (valid_epdp_mt_lemma_name mt_id) (valid_epdp_mt_f mt_id)
  
let hint_simplify_epdp_th_item (mt_id:string) : EcTheory.theory_item =
  let n1 = valid_epdp_op_p in
  let n2 = epdp_mt_op_p mt_id in
  th_item0 (EcTheory.Th_reduction [(
    path_of_string (valid_epdp_mt_lemma_name mt_id),
    { ur_delta = false; ur_eqtrue = true; },
    Some EcTheory.{ 
      rl_tyd  = [];
      rl_vars = [];
      rl_cond = [];
      rl_ptn  = (EcTheory.Rule (`Op (n1,[]), [EcTheory.Rule (`Op (n2,[]),[])]));
      rl_tg   = EcCoreFol.f_true;
      rl_prio = 1; 
    }
    )])

let is_local0 : EcTypes.is_local = `Global

let hint_rewrite_epdp_th_item (mt_id:string) : EcTheory.theory_item =
  let epdp = path_of_string "epdp" in
  let lemma = path_of_string (valid_epdp_mt_lemma_name mt_id) in
  th_item0 (EcTheory.Th_addrw (epdp,[lemma],is_local0))
  
let varpath (mt_id:string) : EcPath.xpath = 
 EcPath.xpath (EcPath.mpath (`Concrete ((EcPath.psymbol mt_id), None)) []) (EcPath.psymbol "i")
  
let ms_body (mt_id:string) : EcModules.module_item list =
  [ MI_Variable { v_name = "i";
                  v_type = EcTypes.tint; 
                };
                  
    MI_Function { f_name = "f_b";
    
                  f_sig  = { fs_name   = "f_b";
                             fs_arg    = EcTypes.tunit;
                             fs_anames = None;
                             fs_ret    = EcTypes.tunit; 
                           };
                           
                  f_def  = FBdef { f_locals = [];
                                   f_body   = EcModules.s_asgn ( LvVar ( EcTypes.pv (varpath mt_id) PVloc,
                                                                         EcTypes.tint
                                                                       ),
                                                                   EcTypes.e_int EcBigInt.one
                                                                 );
                                   f_ret    = None;
                                   f_uses   = EcModules.mk_uses [] EcPath.Sx.empty EcPath.Sx.empty;
                                 }; 
                }
  ]

let module_th_item (mt_id:string) : EcTheory.theory_item =
  let me : EcModules.module_expr = {
    me_name  = mt_id;
    me_body  = ME_Structure { ms_body = ms_body mt_id; };
    me_comps = [];
    me_sig   = { mis_params = [];
                 mis_body   = []; };
  } in
  let tme : EcModules.top_module_expr =
  {
  tme_expr = me;
  tme_loca = locality0;
  } in
  th_item0 (EcTheory.Th_module tme)

let pp_interface (ppf:Format.formatter) (id:string) (it: inter_tyd) : unit =
  let env = EcEnv.Theory.enter id (UcEcInterface.env ()) in
  let clears = [] in
  let tho = EcEnv.Theory.close ~clears is_local0 `Concrete env in
  match tho with
  | Some cth ->
    let msgtys = match unloc it with
                 | BasicTyd b -> IdMap.mapi ec_tydecl_from_msg b
                 | _ -> IdMap.empty 
    in
    let cth_items = IdMap.fold 
      (fun id (_,tydecl) cth_its -> cth_its 
        @ [th_item0 (EcTheory.Th_type (id,tydecl))] 
        @ [enc_op_th_item id]
        @ [dec_op_th_item id]
        @ [epdp_op_th_item id]
        @ [lemma_valid_epdp_th_item id]
        @ [hint_simplify_epdp_th_item id]
        @ [hint_rewrite_epdp_th_item id]
        @ [module_th_item id]) 
      msgtys cth.cth_items in
    let cth_items = (op_pi_th_item "pi") :: cth_items in
    let cth' : EcTheory.ctheory = { 
      cth_items  = cth_items; 
      cth_mode   = cth.cth_mode;
      cth_loca   = cth.cth_loca;
      cth_source = cth.cth_source; }
    in
    let pth = ((path_of_string id), cth') in
    pp_theory ppf pth;
  | None -> print_string "nooooo"
 
let gen_dirs (f:string) (dim: inter_tyd IdMap.t) : unit =
  let fo = open_out (f^".ec") in
  let ppf = Format.formatter_of_out_channel fo in
  IdMap.iter (pp_interface ppf) dim;
  Format.pp_print_flush ppf ();
  close_out fo
  
let generate_ec (ts:typed_spec) : unit =
  let fdim = fileMap ts.dir_inter_map in
  IdMap.iter (fun f dim -> gen_dirs f dim) fdim 

(* clean *)


  
(*---------------------------------------------------------------------------*)
type preamble = [] (* TODO, require/import commands, pi axioms and operators *)

type clone = [] (* TODO, theory cloning info *)

type theory =
  | Clone of clone
  | ECCTh of (EcPath.path * EcTheory.ctheory)
 
type eca = { preamble : preamble; theories : theory list}

let make_theory (id : string) (cth_items : EcTheory.theory) : EcTheory.ctheory =
  let env = EcEnv.Theory.enter id (UcEcInterface.env ()) in
  let clears : EcPath.path list = [] in
  let ctho = EcEnv.Theory.close ~clears is_local0 `Concrete env in
  match ctho with
  | Some cth -> { 
      cth_items  = cth_items; 
      cth_mode   = cth.cth_mode;
      cth_loca   = cth.cth_loca;
      cth_source = cth.cth_source; }
  | None -> failure ("we should be able to make a theory "^id)
  
let make_record (id : string) (fields : (symbol * EcTypes.ty) list) 
: EcDecl.tydecl =
  let tpath = path_of_string id in
  let record = 
    { EI.rc_path = tpath; EI.rc_tparams = []; EI.rc_fields = fields; } in
  let scheme  = EI.indsc_of_record record in
  {
    tyd_params  = record.EI.rc_tparams;
    tyd_type    = `Record (scheme, record.EI.rc_fields); 
    tyd_loca    = locality0;
    tyd_resolve = true;
  }
    
let make_ty (s:string) : EcTypes.ty =
  EcTypes.tconstr (EcPath.psymbol s) []

let addr_ty = make_ty "addr"

let port_ty = make_ty "port"

let msg_fieldname (id : string) (name : string) : string =
  id^"__"^name

let msg_func_fieldname (id : string) : string =
  id^"___func"

let id_ty_pairs (params_map : ty_index IdMap.t) : (symbol * EcTypes.ty) list =
  let params = IdMap.bindings params_map in
  let params = List.map (fun (id,lty_idx) -> (id, unloc lty_idx)) params in
  let params = List.sort (fun a b -> compare (snd(snd a)) (snd(snd b))) params in
  List.map (fun (id,(ty,_)) -> (id,ty)) params

let mb_fields_from_direct_mb (id : string) (mb : message_body_tyd) =
  List.map (fun (n,t) -> (msg_fieldname id n,t)) (id_ty_pairs mb.params_map)

let ec_tydecl_from_direct_mb (id : string) (mb : message_body_tyd) : EcDecl.tydecl =
  let fields = mb_fields_from_direct_mb id mb in
  let port = match mb.port with
             | Some p -> p
             | None -> failure ("messages in direct interfaces have port name")
  in         
  let fields = ((msg_fieldname id port),port_ty)::fields in
  let fields = ((id^"___func"),addr_ty)::fields in
  make_record id fields

let dir_msg_tyd_th_item (id : string) (mb : message_body_tyd) : EcTheory.theory_item =
  th_item0 (EcTheory.Th_type (id, (ec_tydecl_from_direct_mb id mb)))
    
let msg_ty = make_ty "msg"

let enc_op_ty (id : string) =
  EcTypes.tfun (make_ty  id) msg_ty

let int_ty = EcTypes.tint

let op_pi_name = "pi"

let op_pi_path = path_of_string op_pi_name

let op_pi = EcTypes.e_op op_pi_path [] int_ty

let mode_ty = make_ty "mode"

let univ_ty = make_ty "univ"
  
let zero_ex = EcTypes.e_int EcBigInt.zero

let bool_ty = EcTypes.tbool

let and_ex = EcTypes.e_op (path_of_string "/\\") [bool_ty;bool_ty] bool_ty

let and_app b1 b2 = EcTypes.e_app and_ex [b1; b2] bool_ty

let or_ex  = EcTypes.e_op (path_of_string "\\/") [bool_ty;bool_ty] bool_ty

let or_app b1 b2 = EcTypes.e_app or_ex [b1; b2] bool_ty

let not_ex = EcTypes.e_op (path_of_string "[!]") [bool_ty] bool_ty

let not_app b = EcTypes.e_app not_ex [b] bool_ty

let bool_eq_ex  = EcTypes.e_op (path_of_string "=") [bool_ty;bool_ty] bool_ty

let bool_eq_app b1 b2 = EcTypes.e_app bool_eq_ex [b1; b2] bool_ty

let int_eq_ex  = EcTypes.e_op (path_of_string "=") [int_ty;int_ty] bool_ty

let int_eq_app b1 b2 = EcTypes.e_app int_eq_ex [b1; b2] bool_ty

let epdp_ex epdp_name =
  let env = UcEcInterface.env () in
  let _, epdp_t = EcEnv.Op.lookup ([],epdp_name) env in
  let epdp_p = path_of_string epdp_name in
  EcTypes.e_op epdp_p [] epdp_t.op_ty
  
let epdp_enc (epdp_ex : EcTypes.expr) : EcTypes.expr =
  EcTypes.e_proj epdp_ex 0 univ_ty


let epdp_tuple_univ_ex (epdp_ops : EcTypes.expr list) : EcTypes.expr =
  let name =
    match List.length epdp_ops with
    | 2 -> "epdp_pair_univ"
    | 3 -> "epdp_triple_univ"
    | 4 -> "epdp_quadruple_univ"
    | 5 -> "epdp_quintuple_univ"
    | 6 -> "epdp_sextuple_univ"
    | 7 -> "epdp_septuple_univ"
    | 8 -> "epdp_octuple_univ"
    | _ -> failure "epdp_tuples must have size between 2 and 8"
    in
  let env = UcEcInterface.env () in
  let _, epdp_t = EcEnv.Op.lookup (["UCUniv"],name) env in
  let epdp_p = path_of_string name in
  let tys = List.map (fun ex -> EcTypes.e_ty ex) epdp_ops in
  let epdp_tuple_univ_op_ex = EcTypes.e_op epdp_p tys epdp_t.op_ty in
  EcTypes.e_app epdp_tuple_univ_op_ex epdp_ops epdp_t.op_ty
  
let epdp_tyname_univ (ty : EcTypes.ty) : EcTypes.expr =
  let ty_p =
    match ty.ty_node with
    | Tconstr (p,_) -> p
    | _ -> failure ("did not expect "^ (EcTypes.dump_ty ty) )
    in
  print_string ((EcTypes.dump_ty ty)^"\n");
  let epdp_name =
    match EcPath.basename ty_p with
    | "unit" -> "epdp_unit_univ"
    | "bool" -> "epdp_bool_univ"
    | "int"  -> "epdp_int_univ"
    | "addr" -> "epdp_addr_univ"
    | "port" -> "epdp_port_univ"
    | "univ" -> "epdp_id"
    | basename -> failure ("yet unsupported epdp for "^basename
      ^", "^(EcPath.tostring ty_p))
    in
  epdp_ex epdp_name

let get_tys (params_map : ty_index IdMap.t) : EcTypes.ty list =
  snd(List.split (id_ty_pairs params_map))
  
let epdp_data_ex (params_map : ty_index IdMap.t) : EcTypes.expr =
  let tys = get_tys params_map in
  let epdp_ops = List.map epdp_tyname_univ tys in
  match List.length epdp_ops with
  | 0 -> epdp_ex "epdp_unit_univ"
  | 1 -> List.hd epdp_ops
  | _ -> epdp_tuple_univ_ex epdp_ops
  
let epdp_dec_return_dataty (params_map : ty_index IdMap.t) : EcTypes.ty =
  let tys = get_tys params_map in
  let retty =
    match List.length tys with
    | 0 -> EcTypes.tunit
    | 1 -> List.hd tys
    | _ -> EcTypes.ttuple tys
    in
  EcTypes.toption retty
 
let epdp_dec_return_pattern (params_map : ty_index IdMap.t) : EcTypes.lpattern =
  let params = id_ty_pairs params_map in
  match params with
  | [] -> failure "no pattern for messages without data"
  | [(id,ty)] -> EcTypes.LSymbol (EcIdent.create id,ty)
  | _ -> EcTypes.LTuple (List.map (fun (id,ty) -> (EcIdent.create id,ty)) params)

let epdp_dec_make_record_ex (id:string) (params_map : ty_index IdMap.t) : EcTypes.expr =
  EcTypes.e_none (make_ty id)
  
let enc_direct_op_expr (id:string) (mb : message_body_tyd) : EcTypes.expr =
  let mode = EcTypes.e_op (path_of_string "Dir") [] mode_ty in
  let (iden,t) = ((EcIdent.create "x"),(make_ty id)) in
  let x = EcTypes.e_local iden t in
  let xport = EcTypes.e_proj x 1 port_ty in
  let xaddr = EcTypes.e_proj x 0 addr_ty in
  let funport = EcTypes.e_tuple [xaddr;op_pi] in
  let encex = epdp_enc (epdp_data_ex mb.params_map) in
  let tuple =
    match mb.dir with
    | In  -> [mode;funport;xport;zero_ex;encex]
    | Out -> [mode;xport;funport;zero_ex;encex]
    in
  EcTypes.e_lam [(iden,t)] (EcTypes.e_tuple tuple)

let enc_direct_op_body (id:string) (mb : message_body_tyd) = 
  EcDecl.OP_Plain ((enc_direct_op_expr id mb),false)
  
let enc_direct_op (id : string) (mb : message_body_tyd) : EcDecl.operator =
  mk_op0 [] (enc_op_ty id) (Some (enc_direct_op_body id mb))

let dec_direct_op_expr (id:string) (mb : message_body_tyd) : EcTypes.expr =
  let mod_= EcIdent.create "mod" in
  let pt1 = EcIdent.create "pt1" in
  let pt2 = EcIdent.create "pt2" in
  let tag = EcIdent.create "tag" in
  let v   = EcIdent.create "v" in
  let lpattern = EcTypes.LTuple  
    [ (mod_, mode_ty);
      (pt1 , port_ty);
      (pt2 , port_ty); 
      (tag , int_ty ); 
      (v   , univ_ty)
    ]
  in
  
  let m = EcIdent.create "m" in
  let m_ex = EcTypes.e_local m msg_ty in
  
  let mode_Adv = EcTypes.e_op (path_of_string "Adv") [] mode_ty in
  let mod_ex = EcTypes.e_local mod_ mode_ty in
  let c1 = bool_eq_app mod_ex mode_Adv in
  
  let ptproj2 = 
    let pt =
      match mb.dir with
      | In  -> pt1
      | Out -> pt2
      in 
    let pt_ex = EcTypes.e_local pt port_ty in
    EcTypes.e_proj pt_ex 1 int_ty
  in
  let c2 = not_app (int_eq_app ptproj2 op_pi) in
  
  let tag_ex = EcTypes.e_local tag int_ty in
  let c3 = not_app (int_eq_app tag_ex zero_ex) in
  
  let cond = or_app (or_app c1 c2) c3 in
  
  let dec_msg_ty = make_ty id in
  let then_br = EcTypes.e_none dec_msg_ty in
  
  let dec_retty = epdp_dec_return_dataty mb.params_map in
  let dec_ty = EcTypes.tfun univ_ty dec_retty in
  let decex = (EcTypes.e_proj (epdp_data_ex mb.params_map) 1 dec_ty) in
  let v_ex = EcTypes.e_local v univ_ty in
  let mt = EcTypes.e_app decex [v_ex] dec_retty in
  let br_none_body = then_br in
  let br_none = EcTypes.e_lam [] br_none_body in
  
  let p = EcIdent.create "p" in
  let p_ex = EcTypes.e_local p dec_retty in
  let ret_msg_ex = epdp_dec_make_record_ex id mb.params_map in
  let br_some_body = if IdMap.is_empty mb.params_map
    then ret_msg_ex
    else 
      let decpat = epdp_dec_return_pattern mb.params_map in
      EcTypes.e_let decpat p_ex ret_msg_ex
  in
  let br_some = EcTypes.e_lam [(p,dec_retty)] br_some_body in
  let else_br = EcTypes.e_match mt [br_none; br_some] 
    (EcTypes.toption dec_msg_ty) in
  let decode = EcTypes.e_if cond then_br else_br in
  EcTypes.e_let lpattern m_ex decode

let dec_direct_op_body (id:string) (mb : message_body_tyd) = 
  EcDecl.OP_Plain ((dec_direct_op_expr id mb),true)  
  
let dec_direct_op (id : string) (mb : message_body_tyd) : EcDecl.operator =
  mk_op0 [] (dec_op_ty id) (Some (dec_direct_op_body id mb))

let dec_op_ty (id : string) =
  EcTypes.tfun msg_ty (make_ty id)
  
let enc_op_name id = "enc_"^id

let dec_op_name id = "dec_"^id

let enc_direct_op_th_item (id:string) (mb : message_body_tyd) 
: EcTheory.theory_item =
  let op_decl = enc_direct_op id mb in
  let op_name = enc_op_name id in
  op_th_item op_name op_decl
  
let dec_direct_op_th_item (id:string) (mb : message_body_tyd) 
: EcTheory.theory_item =
  let op_decl = dec_direct_op id mb in
  let op_name = dec_op_name id in
  op_th_item op_name op_decl

let nullary_int_op =
  mk_op0 [] int_ty None
  
let op_th_item (id:string) (op:EcDecl.operator) : EcTheory.theory_item =
  th_item0 (EcTheory.Th_operator (id,op))

let direct_msg_theory (id : string) (mb : message_body_tyd)
: EcTheory.theory =
  [ dir_msg_tyd_th_item id mb; 
    enc_direct_op_th_item id mb;
    dec_direct_op_th_item id mb;
    epdp_op_th_item id;
    lemma_valid_epdp_th_item id;
    hint_simplify_epdp_th_item id;
    hint_rewrite_epdp_th_item id
  ]

let pi_op_th_item : EcTheory.theory_item =
  op_th_item op_pi_name nullary_int_op

let inter_th_name (s : symbol) = "UC_"^s

let trans_basic_dir_inter (s : symbol) (b : basic_inter_body_tyd)
: theory =
  let th_name = inter_th_name s in
  let cth_items = IdMap.fold (fun id mb l-> l@(direct_msg_theory id mb)) b [pi_op_th_item] in
  let cth = make_theory th_name cth_items in
  ECCTh ((path_of_string th_name) , cth)

let trans_dir_inter (s : string) (it : inter_tyd) : theory =
    match unloc it with
    | BasicTyd b     -> trans_basic_dir_inter s b
    | CompositeTyd _ -> Clone [] (*TODO*)


let add_dir_inter ((f,n) : string * string) (it : inter_tyd) (em : eca IdMap.t) 
  : eca IdMap.t =
  IdMap.update f 
    (fun eca_opt ->
      let ec_it = trans_dir_inter n it in
      match eca_opt with
      | None -> Some { preamble = []; theories = [ec_it] }
      | Some { preamble = p; theories = t } -> 
        Some { preamble = p; theories = t @ [ec_it] }
    ) em

let translate (ts:typed_spec) : eca IdMap.t =
  let eca_map = IdPairMap.fold add_dir_inter ts.dir_inter_map IdMap.empty in
  eca_map
(*---------------------------------------------------------------------------*)
  
let write_eca (ppf : Format.formatter) (eca : eca) : unit =
  List.iter (
    fun th ->
      match th with
      | Clone _ -> ()
      | ECCTh pth -> pp_theory ppf pth
    ) eca.theories

let ec_filename (f : string) : string = f^".eca"

let open_formatter (f : string) : out_channel * Format.formatter =
  let fo = open_out_gen [Open_append; Open_creat] 0o666 (ec_filename f) in
  let ppf = Format.formatter_of_out_channel fo in
  (fo,ppf)

let close_formatter ((fo,ppf) : out_channel * Format.formatter) : unit =
  Format.pp_print_flush ppf ();
  close_out fo

let gen_ec (eca_map : eca IdMap.t) : unit =
  let remove_file fn =
    if Sys.file_exists fn 
      then Sys.remove fn 
      else () in
  IdMap.iter (
    fun f eca ->
      let fn = ec_filename f in
      remove_file fn;
      let (fo,ppf) = open_formatter f in
      write_eca ppf eca;
      close_formatter (fo,ppf)
    ) eca_map
(*---------------------------------------------------------------------------*)

let generate_ec (ts:typed_spec) : unit =
  gen_ec (translate ts)
  

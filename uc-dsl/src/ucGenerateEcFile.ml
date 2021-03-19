open UcTypedSpec
open EcLocation
module EI = EcInductive

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
  
let pqname_of_string (id:string) =
  let env = UcEcInterface.env () in
  EcPath.pqname (EcEnv.root env) id
(*using ecScope.add_record as a starting point and copying parts of code from
ecScope.add_record, ecHiInductive.trans_record 
*)  
let ec_tydecl_from_msg (id:string) (mb:message_body_tyd) : EcPath.path * EcDecl.tydecl =
  let tpath = pqname_of_string id in
  let fields = IdMap.bindings 
    (IdMap.map (fun til -> let ty,_ = unloc til in ty) mb.params_map) in
  let record = 
    { EI.rc_path = tpath; EI.rc_tparams = []; EI.rc_fields = fields; } in
  let scheme  = EI.indsc_of_record record in
  tpath,
  {
    tyd_params = record.EI.rc_tparams;
    tyd_type   = `Record (scheme, record.EI.rc_fields); }

let nullary_int_op =
  EcDecl.mk_op [] EcTypes.tint None
  
let op_pi_th_item (id:string) : EcTheory.ctheory_item =
  EcTheory.CTh_operator (id,nullary_int_op)
  
let op_th_item (id:string) (op:EcDecl.operator) : EcTheory.ctheory_item =
  EcTheory.CTh_operator (id,op)

let mk_ty_from_s (s:string) : EcTypes.ty =
  EcTypes.tconstr (EcPath.psymbol s) []

let msg_ty = mk_ty_from_s "msg"

let enc_op (mt_id : string) : EcDecl.operator =
  EcDecl.mk_op [] (EcTypes.tfun (mk_ty_from_s mt_id) msg_ty) None

let dec_op (mt_id : string) : EcDecl.operator =
  EcDecl.mk_op [] (EcTypes.tfun msg_ty (mk_ty_from_s mt_id)) None

let enc_op_th_item (mt_id:string) : EcTheory.ctheory_item =
  let op_decl = enc_op mt_id in
  let op_name = "enc_"^mt_id in
  op_th_item op_name op_decl
  
let dec_op_th_item (mt_id:string) : EcTheory.ctheory_item =
  let op_decl = dec_op mt_id in
  let op_name = "dec_"^mt_id in
  op_th_item op_name op_decl

(*let epdp_op_th_item (mt_id:string) : EcTheory.ctheory_item =
  let env = UcEcInterface.env () in
  let epdp_p , epdp_tydecl = EcEnv.Ty.lookup ([],"epdp") env in
  print_string (EcPath.tostring epdp_p);
  (*let epdp_ty = EcEnv.Ty.unfold epdp_p [mk_ty_from_s mt_id; msg_ty] env in*)
  let epdp_rcrd = match epdp_tydecl with
                | ({ tyd_type = `Record rcrd }) -> rcrd
                | _ -> UcMessage.failure "noooo oooo"
                in 
  let epdp_ty = EcDecl.ty_instanciate epdp_tydecl.tyd_params [mk_ty_from_s mt_id; msg_ty] 
  let op_decl = (EcDecl.mk_op [] epdp_ty None) in
  let op_name = "epdp_"^mt_id in
  op_th_item op_name op_decl*)
  
let lemma_th_item : EcTheory.ctheory_item =
  EcTheory.CTh_axiom
  ("tru",
  { ax_tparams = [];
    ax_spec    = EcCoreFol.f_true;
    ax_kind    = `Lemma;
    ax_nosmt   = false 
  })

let pp_interface (ppf:Format.formatter) (id:string) (it: inter_tyd) : unit =
  let env = EcEnv.Theory.enter id (UcEcInterface.env ()) in
  let clears = [] in
  let ctho = EcEnv.Theory.close ~clears env in
  match ctho with
  | Some cth ->
    let msgtys = match unloc it with
                 | BasicTyd b -> IdMap.mapi ec_tydecl_from_msg b
                 | _ -> IdMap.empty 
    in
    let cth_items = IdMap.fold 
      (fun id (_,tydecl) cth_its -> cth_its 
        @ [EcTheory.CTh_type (id,tydecl)] 
        @ [enc_op_th_item id]
        @ [dec_op_th_item id]
        (*@ [epdp_op_th_item id]*)) 
      msgtys cth.cth_struct in
    let cth_items = (op_pi_th_item "pi") :: cth_items in
    let cth_items = cth_items @ [lemma_th_item] in
    let cth':EcTheory.ctheory = { cth_desc = cth.cth_desc; cth_struct = cth_items }
    in
    let pth = ((pqname_of_string id),(cth',`Concrete)) in
    pp_theory ppf pth;
  | None -> print_string "nooooo"
 
let gen_dirs (f:string) (dim: inter_tyd IdMap.t) : unit =
  let fo = open_out (f^".ec") in
  let ppf = Format.formatter_of_out_channel fo in
  IdMap.iter (pp_interface ppf) dim;
  Format.pp_print_flush ppf ();
  close_out fo
  
let generate_ec (ts:typed_spec) : unit =
  (*UcEcInterface.require (UcUtils.dummyloc "UCEncoding") (Some `Import);*)
  let fdim = fileMap ts.dir_inter_map in
  IdMap.iter (fun f dim -> gen_dirs f dim) fdim

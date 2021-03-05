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
    let cths = IdMap.fold 
      (fun id (_,tydecl) cths -> cths @ [EcTheory.CTh_type (id,tydecl)] ) 
      msgtys cth.cth_struct in
    let cth':EcTheory.ctheory = { cth_desc = cth.cth_desc; cth_struct = cths }
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
  let fdim = fileMap ts.dir_inter_map in
  IdMap.iter (fun f dim -> gen_dirs f dim) fdim

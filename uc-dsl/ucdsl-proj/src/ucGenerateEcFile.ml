open UcTypedSpec
open EcParsetree

let stf = Format.std_formatter (*REMOVE*)

let dl = UcUtils.dummyloc

let open_theory (name : string) : unit =
  UcEcInterface.process (GthOpen (`Global, false, dl name))
  
let close_theory (name : string) : unit =
  UcEcInterface.process (GthClose ([], dl name))

let operator (pop : poperator) : unit =
  UcEcInterface.process (Goperator pop)
  
let print_theory (ppf : Format.formatter) (name : string) : unit = 
  let env = UcEcInterface.env () in
  let ppe = EcPrinting.PPEnv.ofenv env in
  let pth = EcEnv.Theory.lookup ([], name) env in
  EcPrinting.pp_theory ppe stf pth; (*REMOVE*)
  EcPrinting.pp_theory ppe ppf pth
  
let pi_op : poperator =
  let pq_int = ([],"int") in
  let pty_int = PTnamed (dl pq_int) in
  let podef = PO_abstr (dl pty_int) in
  {
    po_kind     = `Op;
    po_name     = dl "pi";
    po_aliases  = [];
    po_tags     = [];
    po_tyvars   = None;
    po_args     = [];
    po_def      = podef;
    po_ax       = None;
    po_nosmt    = false;
    po_locality = `Global;
  }
  
let write_message (name : string) (mb : message_body_tyd) : unit = ()
  
let write_basic_dir_int (ppf : Format.formatter) (name : string) (bibt : basic_inter_body_tyd) : unit =
  open_theory name;
  operator pi_op;
  IdMap.iter (fun n mb -> write_message n mb) bibt;
  close_theory name;
  print_theory ppf name
  
let write_dir_int (ppf : Format.formatter) (name : string) (dir_int : inter_tyd) : unit =
  let ibt = EcLocation.unloc dir_int in
  match ibt with
  | BasicTyd  bibt -> write_basic_dir_int ppf name bibt
  | CompositeTyd _ -> print_string "TODO\n"

type singlefile_typed_spec = {
  dir_inter_map : inter_tyd IdMap.t;
  adv_inter_map : inter_tyd IdMap.t;
  fun_map       : fun_tyd IdMap.t;
  sim_map       : sim_tyd IdMap.t
}

let write_require_import_UCBasicTypes (ppf : Format.formatter) : unit =
  let threq = 
    (None,
     [(dl "UCBasicTypes", None)],
     Some `Import) in
  UcEcInterface.process (GthRequire threq);
  Format.fprintf stf "@[require import UCBasicTypes.@]@."; (*REMOVE*)
  Format.fprintf ppf "@[require import UCBasicTypes.@]@." 
     
let write_file (ppf : Format.formatter) (sts : singlefile_typed_spec) : unit =
  write_require_import_UCBasicTypes ppf;
  IdMap.iter (fun n d -> write_dir_int ppf n d) sts.dir_inter_map

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
  

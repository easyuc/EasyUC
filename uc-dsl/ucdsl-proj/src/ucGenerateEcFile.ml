open UcTypedSpec
open EcParsetree

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
  EcPrinting.pp_theory ppe Format.std_formatter pth;
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
  
let write_dir_int (ppf : Format.formatter) (name : string) (dir_int : inter_tyd) : unit =
  open_theory name;
  operator pi_op;
  close_theory name;
  print_theory ppf name

(*---------------------------------------------------------------------------*)

let ec_filename (f : string) : string = f^".eca"

let open_formatter (f : string) : out_channel * Format.formatter =
  let fo = open_out_gen [Open_append; Open_creat] 0o666 (ec_filename f) in
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

let generate_ec (ts:typed_spec) : unit =
  let ((fn, n), di) = IdPairMap.min_binding ts.dir_inter_map in
  let fn = ec_filename fn in
  remove_file fn;
  let (fo,ppf) = open_formatter fn in
  write_dir_int ppf n di;
  close_formatter (fo,ppf)
  

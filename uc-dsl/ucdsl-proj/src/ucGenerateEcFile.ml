open UcTypedSpec
  
(*---------------------------------------------------------------------------*)
type preamble = string list(* TODO, require/import commands, pi axioms and operators *)

type clone = string list(* TODO, theory cloning info *)

type theory =
  | Clone of clone
  | ECCTh of (EcPath.path * EcTheory.ctheory)
 
type eca = { preamble : preamble; theories : theory list}

let translate (ts:typed_spec) : eca IdMap.t = IdMap.empty
(*---------------------------------------------------------------------------*)
  
let write_eca (ppf : Format.formatter) (eca : eca) : unit = ()

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
  

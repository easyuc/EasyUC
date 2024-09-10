(* ucdsl.ml *)

(* UC DSL Tool main file *)

open Arg
open Batteries
open UcMessage
open UcParseAndTypecheckFile

let () = Printexc.record_backtrace true

(* order is *opposite* to the order of the -I options *)

let include_dirs_ref : string list ref = ref []

let include_arg (s : string) =
  (include_dirs_ref := s :: (! include_dirs_ref); ())

let anony_arg_ref : string list ref = ref []

let anony_arg (s : string) =
  (anony_arg_ref := (! anony_arg_ref) @ [s]; ())

let raw_msg_ref : bool ref = ref false

let raw_msg_arg () =
  (raw_msg_ref := true; ())

let units_ref : bool ref = ref false

let units_arg () =
  (units_ref := true; ())

let margin_ref : int ref = ref 78

let margin_arg n =
  (margin_ref := n; ())

let interpreter_ref : bool ref = ref false

let interpreter_arg () =
  (interpreter_ref := true; ())

let debug_ref : bool ref = ref false

let debug_arg () =
  (debug_ref := true; ())

let batch_ref : bool ref = ref false

let batch_arg () =
  (batch_ref := true; ())

let version_ref : bool ref = ref false

let version_arg () =
  (version_ref := true; ())

let run_print_pos_ref : bool ref = ref false

let run_print_pos_arg () =
  (run_print_pos_ref := true; ())

let gen_ref : bool ref = ref false

let gen_arg () =
  (
    units_arg ();
    gen_ref := true;
    ()
  )

let arg_specs =
  [("-I", String include_arg, "<dir> Add directory to include search path");
   ("-include", String include_arg,
    "<dir> Add directory to include search path");
   ("-margin", Int margin_arg,
    "<n> Set pretty printing margin (default is 78)");
   ("-raw-msg", Unit raw_msg_arg, "Issue raw messages, for Emacs UC DSL mode");
   ("-units", Unit units_arg, "Require grouping definitions into units");
   ("-interpreter", Unit interpreter_arg,
    "Run interpreter; implicit on .uci file; omit file to run interactively");
   ("-debug", Unit debug_arg, "Print interpeter debugging messages");
   ("-batch", Unit batch_arg, "Run interpreter in batch mode on .uci file");
   ("-gen", Unit gen_arg, "Generate easycrypt files");
   ("-run-print-pos", Unit run_print_pos_arg, "Print .uc file positions while executing interpreter run command for .uci file");
   ("-version", Unit version_arg, "Print version and exit")
  ]

let () = parse arg_specs anony_arg "Usage: ucdsl [options] file"

let () =
  if ! version_ref
  then (Printf.printf "%s\n" UcVersionDoNotEdit.version;
        exit 0)

let error_and_exit (ppf : Format.formatter -> unit) : unit =
  ppf Format.err_formatter;
  Format.pp_print_newline Format.err_formatter ();
  exit 1

let () =
  List.iter
  (fun x ->
     if (not (Sys.file_exists x) || not (Sys.is_directory x))
     then error_and_exit
          (fun ppf ->
             Format.fprintf ppf
             "@[does@ not@ exist@ or@ is@ not@ a@ directory:@ %s@]" x))
  (! include_dirs_ref)

let () = UcState.set_include_dirs (! include_dirs_ref)

let () =
  let n = ! margin_ref in
  if n < 3
  then error_and_exit
       (fun ppf ->
          Format.fprintf ppf
          "@[invalid@ pretty@ printer@ margin:@ %d@]" n)
  else (Format.pp_set_margin Format.std_formatter n;
        Format.pp_set_margin Format.err_formatter n)

let check_file_exists (file : string) : unit =
  if not (Sys.file_exists file)
  then error_and_exit
       (fun ppf ->
          Format.fprintf ppf
          "@[file@ does@ not@ exist:@ %s@]" file)

(* file ends in ".uc" *)

let check_uc_file (file : string) : unit =
  let forbid_option (opt : string) : unit =
    error_and_exit
    (fun ppf ->
       Format.fprintf ppf
       "@[-%s@ option@ not@ allowed@ when@ checking@ .uc@ file@]"
       opt) in
  let () = if ! raw_msg_ref then UcState.set_raw_messages () in
  let () = if ! units_ref then UcState.set_units () in
  let () = if ! interpreter_ref then forbid_option "interpreter" in
  let () = if ! debug_ref then forbid_option "debug" in
  let () = if ! batch_ref then forbid_option "batch" in
  let () = if ! run_print_pos_ref then forbid_option "run_print_pos" in
  let dir = Filename.dirname file in
  let () = UcState.add_highest_include_dirs dir in
  let () = UcEcInterface.init () in
  try
    (let maps = parse_and_typecheck_file_or_id (FOID_File file) in
     if ! gen_ref then UcGenerateEcFile.generate_ec maps
     ;
     exit 0) with
  | ErrorMessageExn -> exit 1

(* file ends in ".uc" *)

let interpreter_file (file : string) : unit =
  let forbid_option (opt : string) : unit =
    error_and_exit
    (fun ppf ->
       Format.fprintf ppf
       "@[-%s@ option@ not@ allowed@ when@ checking@ .uci@ file@]"
       opt) in
  let () = UcState.set_units () in
  let () = if ! raw_msg_ref then forbid_option "raw_msg" in
  let () = if ! batch_ref then UcState.set_batch_mode () in
  let () = if ! debug_ref then UcState.set_debugging () in
  let () = if ! run_print_pos_ref && not ! batch_ref
           then UcState.set_run_print_pos () in
  let dir = Filename.dirname file in
  let () = UcState.add_highest_include_dirs dir in
  let () = UcEcInterface.init() in
  try (UcInterpreterClient.file_client file; exit 0) with
  | ErrorMessageExn -> exit 1

let interpreter_std_in () : unit =
  let forbid_option (opt : string) : unit =
    error_and_exit
    (fun ppf ->
       Format.fprintf ppf
       ("@[-%s@ option@ not@ allowed@ when@ running@ interpreter@ " ^^
        "from@ standard@ input@]")
       opt) in
  let () = UcState.set_units () in
  let () = if ! raw_msg_ref then forbid_option "raw_msg" in
  let () = if ! batch_ref then forbid_option "batch" in
  let () = if ! debug_ref then UcState.set_debugging () in
  let () = UcEcInterface.init() in
  UcInterpreterClient.std_IO_client (); exit 0

let () =
  match ! anony_arg_ref with
  | [file]                    ->
      (match Filename.extension file with
       | ".uc"  -> (check_file_exists file; check_uc_file file)
       | ".uci" -> (check_file_exists file; interpreter_file file)
       | _      ->
           error_and_exit
           (fun ppf ->
              Format.fprintf ppf
              "@[file@ lacks@ \".uc\"@ or@ \".uci\"@ suffix:@ %s@]" file))
  | [] when ! interpreter_ref -> interpreter_std_in ()
  | _                         ->
      (usage arg_specs "Usage: ucdsl [options] file";
       exit 1)

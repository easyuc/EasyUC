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

let debugging_ref : bool ref = ref false

let debugging_arg () =
  (debugging_ref := true; ())

let batch_ref : bool ref = ref false

let batch_arg () =
  (batch_ref := true; ())

let interpreter_ref : bool ref = ref false

let interpreter_arg () =
  (interpreter_ref := true; ())

let arg_specs =
  [("-I", String include_arg, "<dir> Add directory to include search path");
   ("-include", String include_arg,
    "<dir> Add directory to include search path");
   ("-raw-msg", Unit raw_msg_arg, "Issue raw messages");
   ("-units", Unit units_arg, "Require grouping definitions into units");
   ("-margin", Int margin_arg,
    "<n> Set pretty printing margin (default is 78)");
   ("-debug", Unit debugging_arg, "Print interpeter debugging messages");
   ("-batch", Unit batch_arg, "Run interpreter in batch mode");
   ("-interpreter", Unit interpreter_arg, "Run interpreter, implicit with -batch arg or when file ends with .uci. To run interpreter in interactive mode, omit the file argument." )]

let () = parse arg_specs anony_arg "Usage: ucdsl [options] file"

let () =
  List.iter
  (fun x ->
     if (not (Sys.file_exists x) || not (Sys.is_directory x))
     then non_loc_error_message_exit
          (fun ppf ->
             Format.fprintf ppf
             "@[does@ not@ exist@ or@ is@ not@ a@ directory:@ %s@]" x))
  (! include_dirs_ref)

let () = UcState.set_include_dirs (! include_dirs_ref)

let file =
  let files = ! anony_arg_ref in
  match files with
  | [file] -> Some file
  | [] when ! interpreter_ref -> None
  | _      ->
      (usage arg_specs "Usage: ucdsl [options] file";
       exit 1)

let () =
  if ! raw_msg_ref then UcState.set_raw_messages ()

let () =
  if ! units_ref then UcState.set_units()

let () =
  let n = ! margin_ref in
  if n < 3
  then non_loc_error_message_exit
       (fun ppf ->
          Format.fprintf ppf
          "@[invalid@ pretty@ printer@ margin:@ %d@]" n)
  else (Format.pp_set_margin Format.std_formatter n;
        Format.pp_set_margin Format.err_formatter n)

let () =
  if ! debugging_ref then UcState.set_debugging ()

let () =
  if ! batch_ref then 
  begin
    UcState.set_batch_mode (); interpreter_arg ()
  end

let () =
  if file <> None 
  then begin
    let file = Option.get file in
    let ext = Filename.extension file in
    if (ext = ".uci") then interpreter_arg ()
    ;
    if (ext  <> ".uc" && ext <> ".uci")
    then non_loc_error_message_exit
         (fun ppf ->
            Format.fprintf ppf
            "@[file@ lacks@ \".uc\"@ or@ \".uci\"@ suffix:@ %s@]" file)
    else if not (Sys.file_exists file)
    then non_loc_error_message_exit
         (fun ppf ->
            Format.fprintf ppf
            "@[file@ does@ not@ exist:@ %s@]" file)
  else 
  let dir = Filename.dirname file in
       UcState.add_highest_include_dirs dir
  end

let () =
  UcEcInterface.init ();
  try
    if ! interpreter_ref
    then begin
      if file = None
      then UcInterpreterClient.stdIOclient ()
      else UcInterpreterClient.file_client (Option.get file)
    end else begin
      ignore (parse_and_typecheck_file_or_id (FOID_File (Option.get file)));
      exit 0
    end
  with ErrorMessageExn -> exit 1

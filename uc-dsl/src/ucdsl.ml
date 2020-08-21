(* ucdsl.ml *)

(* UC DSL Tool main file *)

open Arg
open UcMessage
open UcParseAndTypecheckFile

let () = Printexc.record_backtrace true

let include_dirs_ref : string list ref = ref []

let include_arg (s : string) =
  (include_dirs_ref := (! include_dirs_ref) @ [s]; ())

let anony_arg_ref : string list ref = ref []

let anony_arg (s : string) =
  (anony_arg_ref := (! anony_arg_ref) @ [s]; ())

let raw_msg_ref : bool ref = ref false

let raw_msg_arg () =
  (raw_msg_ref := true; ())

let arg_specs =
  [("-I", String include_arg, "<dir> Add directory to include search path");
   ("-include", String include_arg,
    "<dir> Add directory to include search path");
   ("-raw-msg", Unit raw_msg_arg, "Issue raw messages")]

let () = parse arg_specs anony_arg "Usage: ucdsl [options] file"

let () =
  List.iter
  (fun x ->
     if (not (Sys.file_exists x) || not (Sys.is_directory x))
     then (non_loc_error_message
           (Printf.sprintf "does not exist or is not a directory: %s" x))
     else())
  (! include_dirs_ref)

let () = UcState.set_include_dirs (! include_dirs_ref)

let file =
  let files = ! anony_arg_ref in
  match files with
    [file] -> file
  | _      ->
      (usage arg_specs "Usage: ucdsl [options] file";
       exit 1)

let () =
  if ! raw_msg_ref then UcState.set_raw_messages() else ()

let () =
  let len = String.length file in
  if len < 4 || String.sub file (len - 3) 3 <> ".uc" then
    (non_loc_error_message
     (Printf.sprintf "file lacks \".uc\" suffix: %s" file))
  else ()

let () =
  (ignore (parse_and_typecheck_file file);
   exit 0)

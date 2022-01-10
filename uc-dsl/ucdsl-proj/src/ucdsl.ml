(* ucdsl.ml *)

(* UC DSL Tool main file *)

(* --------------------------------------------------------------------
 * Copyright (c) - 2020-2021 - Boston University
 *
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

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

let arg_specs =
  [("-I", String include_arg, "<dir> Add directory to include search path");
   ("-include", String include_arg,
    "<dir> Add directory to include search path");
   ("-raw-msg", Unit raw_msg_arg, "Issue raw messages");
   ("-units", Unit units_arg, "Require grouping definitions into units");
   ("-margin", Int margin_arg,
    "<n> Set pretty printing margin (default is 78)")]

let () = parse arg_specs anony_arg "Usage: ucdsl [options] file"

let () =
  List.iter
  (fun x ->
     if (not (Sys.file_exists x) || not (Sys.is_directory x))
     then non_loc_error_message
          (fun ppf ->
             Format.fprintf ppf
             "@[does@ not@ exist@ or@ is@ not@ a@ directory:@ %s@]" x))
  (! include_dirs_ref)

let () = UcState.set_include_dirs (! include_dirs_ref)

let file =
  let files = ! anony_arg_ref in
  match files with
  | [file] -> file
  | _      ->
      (usage arg_specs "Usage: ucdsl [options] file";
       exit 1)

let () =
  if ! raw_msg_ref then UcState.set_raw_messages()

let () =
  if ! units_ref then UcState.set_units()

let () =
  let n = ! margin_ref in
  if n < 3
  then non_loc_error_message
       (fun ppf ->
          Format.fprintf ppf
          "@[invalid@ pretty@ printer@ margin:@ %d@]" n)
  else (Format.pp_set_margin Format.std_formatter n;
        Format.pp_set_margin Format.err_formatter n)

let () =
  let len = String.length file in
  if len < 4 || String.sub file (len - 3) 3 <> ".uc"
    then non_loc_error_message
         (fun ppf ->
            Format.fprintf ppf
            "@[file@ lacks@ \".uc\"@ suffix:@ %s@]" file)
  else if not (Sys.file_exists file)
    then non_loc_error_message
         (fun ppf ->
            Format.fprintf ppf
            "@[file@ does@ not@ exist:@ %s@]" file)
  else let dir = Filename.dirname file in
       UcState.add_highest_include_dirs dir

let () =
  UcEcInterface.init ();
  ignore (parse_and_typecheck_file_or_id (FOID_File file));
  exit 0

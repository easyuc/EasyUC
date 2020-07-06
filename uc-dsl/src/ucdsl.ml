(* ucdsl.ml *)

(* UC DSL Tool main file *)

open Arg
open UcParseAndTypecheckFile
open UcUtils

let () = Printexc.record_backtrace true

let include_dirs_ref : string list ref = ref []

let include_arg (s : string) =
  (include_dirs_ref := (! include_dirs_ref) @ [s]; ())

let anony_arg_ref : string list ref = ref []

let anony_arg (s : string) =
  (anony_arg_ref := (! anony_arg_ref) @ [s]; ())

let arg_specs =
  [("-I", String include_arg, "<dir> add directory to include search path");
   ("-include", String include_arg,
    "<dir> add directory to include search path")]

let () = parse arg_specs anony_arg "Usage: ucdsl [options] file"

let () =
  List.iter
  (fun x ->
     if (not (Sys.file_exists x) || not (Sys.is_directory x))
     then (Printf.fprintf stderr "does not exist or is not a directory: %s\n" x;
           exit 1)
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
  let len = String.length file in
  if len < 4 || String.sub file (len - 3) 3 <> ".uc"
  then (Printf.fprintf stderr "file lacks \".uc\" suffix: %s\n" file;
        exit 1)
  else ()

let ch =
  try open_in file with
    Sys_error _ ->
      (Printf.fprintf stderr "unable to open file: %s\n" file;
       exit 1)

let () = try ignore (parse_and_typecheck_file ch) with exn -> printEx exn

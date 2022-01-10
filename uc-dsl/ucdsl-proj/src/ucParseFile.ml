(* UcParseFile module *)

(* Parse a DSL Specification *)

(* --------------------------------------------------------------------
 * Copyright (c) - 2020-2021 - Boston University
 *
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

open EcLocation
open EcSymbols
open UcMessage
open UcLexer
module L = Lexing

let lexbuf_from_channel file ch =
  let lexbuf = Lexing.from_channel ch in
    lexbuf.Lexing.lex_curr_p <- {
        Lexing.pos_fname = file;
        Lexing.pos_lnum  = 1;
        Lexing.pos_bol   = 0;
        Lexing.pos_cnum  = 0
      };
    lexbuf

type file_or_id =
  (* file name, interpreted relative to working directory, if not
      fully qualified *)
  | FOID_File of string
  (* root name of .uc file, initial letter capitalized, and without
     ".uc" and without "/"s, normally located in file that was lexed *)
  | FOID_Id   of symbol located

let foid_to_str foid =
  match foid with
  | FOID_File s  -> s
  | FOID_Id   id -> unloc id

let parse_file_or_id foid =
  let prelude_dir = UcConfig.uc_prelude_dir in
  let inc_dirs = UcState.get_include_dirs () in
  let (ch, file) =
    match foid with
    | FOID_File file ->
        (try (open_in file, file) with
         | Sys_error _ ->
             non_loc_error_message
             (fun ppf ->
                Format.fprintf ppf
                "@[unable@ to@ open@ file:@ %s@]" file))
    | FOID_Id id     ->
        let uid = unloc id in
        (match UcUtils.find_file uid ".uc" prelude_dir inc_dirs with
         | None           ->
             error_message (loc id)
             (fun ppf ->
                Format.fprintf ppf
                "@[unable@ to@ find@ .uc@ file:@ %s@]" uid)
         | Some qual_file ->
             (try (open_in qual_file, qual_file) with
              | Sys_error _ ->
                  error_message (loc id)
                  (fun ppf ->
                     Format.fprintf ppf
                     "@[unable@ to@ open@ file:@ %s@]" qual_file))) in
  let lexbuf = lexbuf_from_channel file ch in  
  try (let res = (UcParser.spec read lexbuf, file) in
       close_in ch; res) with
  | UcParser.Error ->
      (error_message  (* no need to close channel *)
       (EcLocation.make lexbuf.L.lex_start_p lexbuf.L.lex_curr_p)
       (fun ppf -> Format.fprintf ppf "@[parse@ error@]"))

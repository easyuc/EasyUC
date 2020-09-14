(* UcParseFile module *)

(* parse a DSL Specification *)

open EcLocation
open UcMessage
open UcLexer
module L = Lexing
open UcSpec

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
  | FOIDFile of string
  | FOIDId   of id

let foid_to_str foid =
  match foid with
  | FOIDFile s  -> s
  | FOIDId   id -> unloc id

let parse_file_or_id foid =
  let (ch, file) =
    match foid with
    | FOIDFile file ->
        (try open_in file, file with
         | Sys_error _ ->
             non_loc_error_message
             (fun ppf ->
                Format.fprintf ppf
                "@[unable@ to@ open@ file:@ %s@]" file))
    | FOIDId id     ->
        let uid = unloc id in
        (try open_in uid, uid with
         | Sys_error _ ->
             error_message (loc id)
             (fun ppf ->
                Format.fprintf ppf
                "@[unable@ to@ open@ file:@ %s@]" (unloc id))) in
  let lexbuf = lexbuf_from_channel file ch in
  try UcParser.spec read lexbuf with
  | UcParser.Error ->
      (error_message
       (EcLocation.make lexbuf.L.lex_start_p lexbuf.L.lex_curr_p)
       (fun ppf -> Format.fprintf ppf "@[parse@ error@]"))

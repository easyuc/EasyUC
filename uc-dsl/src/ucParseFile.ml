(* UcParseFile module *)

(* parse a DSL Specification *)

open UcMessage
open UcLexer
open UcSpec
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

let parse_file file =
  let ch =
    try open_in file with
      Sys_error _ ->
        non_loc_error_message ("unable to open file: " ^ file) in
  let lexbuf = lexbuf_from_channel file ch in
  try UcParser.spec read lexbuf with
  | UcParser.Error ->
      (error_message
       (EcLocation.make lexbuf.L.lex_start_p lexbuf.L.lex_curr_p)
       "parse error")
  | LexerError (loc, msg) -> error_message loc msg
  | ParseError (loc, msg) -> error_message loc msg

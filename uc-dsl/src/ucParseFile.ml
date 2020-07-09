(* UcParseFile module *)

(* parse a DSL Specification *)

open UcMessage
open UcLexer
open UcSpec
module L = Lexing

let parse_file file =
  let ch =
    try open_in file with
      Sys_error _ ->
        error_message file None "unable to open file" in
  let lexbuf = Lexing.from_channel ch in
  try UcParser.spec read lexbuf with
  | UcParser.Error ->
      (error_message
       file
       (Some (EcLocation.make lexbuf.L.lex_start_p lexbuf.L.lex_curr_p))
       "parse error")
  | LexerError (loc, msg) ->
      error_message file (Some loc) msg
  | ParseError (loc, msg) ->
      error_message file (Some loc) msg

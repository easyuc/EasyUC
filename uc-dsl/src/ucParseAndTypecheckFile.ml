(* ucParseAndTypecheckFile.ml *)

(* Parse and then typecheck a DSL specification *)

open UcLexer
open UcParser
open UcTypecheck
open UcSpec
module L = Lexing

let read_to_eof ch =
  let rec reads xs =
    match try Some (input_line ch) with
            End_of_file -> None with
      None   -> String.concat "" (List.rev xs)
    | Some x -> reads ((x ^ "\n") :: xs)
  in reads []

let parse_and_typecheck_file ch =
  let s = read_to_eof ch in
  let lexbuf = L.from_string s in
  let spec =
    try spec read lexbuf with
      Error ->
        parse_error
        (EcLocation.make lexbuf.L.lex_start_p lexbuf.L.lex_curr_p)
        None in
  typecheck spec

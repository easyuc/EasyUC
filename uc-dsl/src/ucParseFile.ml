(* UcParseFile module *)

(* parse a DSL Specification *)

open UcLexer
open UcParser
open UcSpec
module L = Lexing

let read_to_eof ch =
  let rec reads xs =
    match try Some (input_line ch) with
            End_of_file -> None with
      None   -> String.concat "" (List.rev xs)
    | Some x -> reads ((x ^ "\n") :: xs)
  in reads []

let parse_file ch =
  let s = read_to_eof ch in
  let lexbuf = L.from_string s in
  try spec read lexbuf with
    Error ->
      parse_error
      (EcLocation.make lexbuf.L.lex_start_p lexbuf.L.lex_curr_p)
      None

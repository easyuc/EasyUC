open DlLexer
open DlParser
open Dl
open DlParseTree
module L = Lexing
open DlUtils

(*from https://stackoverflow.com/questions/53839695/how-do-i-read-the-entire-content-of-a-given-file-into-a-string*)
let read_whole_file filename =
    let ch = open_in filename in
    let s = really_input_string ch (in_channel_length ch) in
    close_in ch;
    s

let read_file filename = read_whole_file (filename)

let parse_file filename =
  let s = read_file filename in
  let lexbuf = Lexing.from_string s in
  let ast = try
		prog read lexbuf
	    with
	    Error -> parse_error (EcLocation.make lexbuf.L.lex_start_p lexbuf.L.lex_curr_p ) None
  in
  checkDL ast



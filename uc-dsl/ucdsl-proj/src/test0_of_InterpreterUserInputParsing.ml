let parse_error_handling lexbuf =
 UcMessage.error_message  (* no need to close channel *)
 (EcLocation.make lexbuf.Lexing.lex_start_p lexbuf.Lexing.lex_curr_p)
 (fun ppf -> Format.fprintf ppf "@[parse@ error@]")

let parse_fun_expr (fe : string) : UcSpec.fun_expr =
  let lexbuf = Lexing.from_string fe in
  try UcParser.fun_expr_start UcLexer.read lexbuf  with
  | UcParser.Error -> parse_error_handling lexbuf
      
let parse_sent_msg_expr (sme : string) : UcSpec.sent_msg_expr =
  let lexbuf = Lexing.from_string sme in
  try UcParser.sent_msg_expr_start UcLexer.read lexbuf  with
  | UcParser.Error -> parse_error_handling lexbuf
  
let () : unit =
  let _ = parse_fun_expr "ThisFunHasNoArgs" in
  let _ = parse_fun_expr "FunWith0Args()" in
  let _ = parse_fun_expr "FunWith1Arg(FunWithNoArgs)" in
  
  let _ = parse_sent_msg_expr "(7)@Bla.Bla.bla(1,2,3)$(5)" in
  let _ = parse_sent_msg_expr "iden_in@Bla.Bla.bla(1,2,3)$iden_out" in
  ()

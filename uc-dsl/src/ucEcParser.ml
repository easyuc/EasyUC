open EcUtils
open EcLocation

module P = EcParser
module L = Lexing


(*copied some code from ecIo.ml since we need stuff not exposed by .mli *)
(*couldn't make this solution work: 
https://stackoverflow.com/questions/35098936/ignore-ocaml-interfaces-with-ocamlbuild *)
(* -------------------------------------------------------------------- *)

type 'a parser_t =
  (P.token * L.position * L.position, 'a) MenhirLib.Convert.revised


(* -------------------------------------------------------------------- *)
type 'a ecreader_gr = {
  (*---*) ecr_lexbuf  : Lexing.lexbuf;
  (*---*) ecr_parser  : 'a parser_t;
  mutable ecr_tokens  : EcParser.token list;
  mutable ecr_atstart : bool;
}

type 'a ecreader_g = 'a ecreader_gr Disposable.t

(* -------------------------------------------------------------------- *)
let lexbuf (reader : 'a ecreader_g) =
  (Disposable.get reader).ecr_lexbuf

(* -------------------------------------------------------------------- *)

let finalize (ecreader : 'a ecreader_g) =
  Disposable.dispose ecreader

(* -------------------------------------------------------------------- *)
let lexer = fun ecreader ->
  let lexbuf = ecreader.ecr_lexbuf in

  if ecreader.ecr_tokens = [] then
    ecreader.ecr_tokens <- EcLexer.main lexbuf;
  match ecreader.ecr_tokens with
  | [] ->
      failwith "short-read-from-lexer"

  | token :: queue -> begin
      ecreader.ecr_tokens  <- queue;
      ecreader.ecr_atstart <- (token = EcParser.FINAL);
      (token, Lexing.lexeme_start_p lexbuf, Lexing.lexeme_end_p lexbuf)
  end



(* -------------------------------------------------------------------- *)
let parse (ecreader : 'a ecreader_g) =
  let ecreader = Disposable.get ecreader in
    ecreader.ecr_parser (fun () -> lexer ecreader)

(* -------------------------------------------------------------------- *)

(*EC local declaration parser*)

let locDeclParserfun = fun () ->
    MenhirLib.Convert.Simplified.traditional2revised EcParser.loc_decl

type ecVarDeclReader = EcParsetree.pfunction_local ecreader_g

let ecVarDeclReader_from_string data =
  let lexbuf = Lexing.from_string data in

    Disposable.create
      { ecr_lexbuf  = lexbuf;
        ecr_parser  = locDeclParserfun ();
        ecr_atstart = true;
        ecr_tokens  = []; }

let ecVarDecl s = parse (ecVarDeclReader_from_string s)

(*EC expression parser*)

let exprParserfun = fun () ->
    MenhirLib.Convert.Simplified.traditional2revised EcParser.expr_u

type ecExprReader = EcParsetree.pexpr_r ecreader_g

let ecExprReader_from_string data =
  let lexbuf = Lexing.from_string data in

    Disposable.create
      { ecr_lexbuf  = lexbuf;
        ecr_parser  = exprParserfun ();
        ecr_atstart = true;
        ecr_tokens  = []; }

let ecExpr s = parse (ecExprReader_from_string s)

(*EC statement parser*)

let stmtParserfun = fun () ->
    MenhirLib.Convert.Simplified.traditional2revised EcParser.stmt

type ecStmtReader = EcParsetree.pstmt ecreader_g

let ecStmtReader_from_string data =
  let lexbuf = Lexing.from_string data in

    Disposable.create
      { ecr_lexbuf  = lexbuf;
        ecr_parser  = stmtParserfun ();
        ecr_atstart = true;
        ecr_tokens  = []; }

let ecStmt s = parse (ecStmtReader_from_string s)





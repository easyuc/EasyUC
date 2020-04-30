
(* The type of tokens. *)

type token = 
  | WITH
  | VAR
  | USES
  | UNDERSCORE
  | TRANSITION
  | SUBFUN
  | STATE
  | STAR
  | SIMS
  | SIM
  | SERVES
  | SEND
  | SEMICOLON
  | RPAREN
  | ROP4 of (string)
  | REQUIRES
  | RBRACE
  | PIPE
  | PARTY
  | OUT
  | OTHERMSG
  | OR
  | OK
  | NOT
  | MESSAGE
  | MATCH
  | LPAREN
  | LBRACE
  | INITIAL
  | IN
  | IMPORT
  | IMPLEM
  | IF
  | ID of (string)
  | HAT
  | FUNCT
  | FAIL
  | ERROR
  | EQ
  | EOF
  | END
  | ENCODE
  | ELSE
  | ELIF
  | DOT
  | DIRIO
  | DECODE
  | COMMA
  | COLON
  | AT
  | ASGVAL
  | ASGSAMPLE
  | AS
  | ARROW
  | ANDTXT
  | AND
  | ADVIO

(* This exception is raised by the monolithic API functions. *)

exception Error

(* The monolithic API. *)

val prog: (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (DlParseTree.dlprog)

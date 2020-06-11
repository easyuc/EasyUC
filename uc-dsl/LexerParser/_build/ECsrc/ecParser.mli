
(* The type of tokens. *)

type token = 
  | ZETA
  | WP
  | WLOG
  | WITH
  | WHY3
  | WHILE
  | VAR
  | UNROLL
  | UNDO
  | UNDERSCORE
  | UINT of (EcBigInt.zint)
  | UIDENT of (EcSymbols.symbol)
  | TYPE
  | TRY
  | TRIVIAL
  | TRANSITIVITY
  | TOP
  | TIMEOUT
  | TIME
  | TILD
  | TIDENT of (EcSymbols.symbol)
  | TICKPIPE
  | THEORY
  | THEN
  | SYMMETRY
  | SWAP
  | SUFF
  | SUBST
  | STRING of (string)
  | STRICT
  | STAR
  | SPLITWHILE
  | SPLIT
  | SP
  | SOLVE
  | SMT
  | SLASHTILDEQ
  | SLASHSLASHTILDEQ
  | SLASHSLASHSHARP
  | SLASHSLASHGT
  | SLASHSLASHEQ
  | SLASHSLASH
  | SLASHSHARP
  | SLASHGT
  | SLASHEQ
  | SLASH
  | SKIP
  | SIMPLIFY
  | SIM
  | SHARPPIPE
  | SHARP
  | SEQ
  | SEMICOLON
  | SELF
  | SECTION
  | SEARCH
  | RWNORMAL
  | RRARROW
  | RPBRACE
  | RPAREN
  | ROP4 of (string)
  | ROP3 of (string)
  | ROP2 of (string)
  | ROP1 of (string)
  | RND
  | RING of ([`Raw|`Eq])
  | RIGHT
  | REWRITE
  | RETURN
  | RES
  | REQUIRE
  | REPLACE
  | RENAME
  | REMOVE
  | REFLEX
  | REALIZE
  | RCONDT
  | RCONDF
  | RBRACKET
  | RBRACE
  | RBOOL
  | RARROW
  | QUESTION
  | QED
  | PUNIOP of (EcSymbols.symbol)
  | PROVER
  | PROOF
  | PROGRESS
  | PROC
  | PRINT
  | PRED
  | PRBOUNDED
  | PRAGMA
  | PR
  | POSE
  | PNUMOP of (EcSymbols.symbol)
  | PLUS
  | PIPEPIPEGT
  | PIPEGT
  | PIPE
  | PHOARE
  | PCENT
  | PBINOP of (EcSymbols.symbol)
  | ORA
  | OR
  | OP
  | OF
  | NUMOP of (string)
  | NOTATION
  | NOT
  | NOSMT
  | NOP of (string)
  | NE
  | MOVE
  | MODULE
  | MODPATH
  | MINUS
  | MIDENT of (EcSymbols.symbol)
  | MATCH
  | LTSTARGTGT
  | LTSTARGT
  | LTLTSTARGT
  | LTCOLON
  | LT
  | LPBRACE
  | LPAREN
  | LOSSLESS
  | LOP4 of (string)
  | LOP3 of (string)
  | LOP2 of (string)
  | LOP1 of (string)
  | LONGARROW
  | LOGIC
  | LOCAL
  | LLARROW
  | LIDENT of (EcSymbols.symbol)
  | LET
  | LESAMPLE
  | LEMMA
  | LEFT
  | LEAT
  | LE
  | LBRACKET
  | LBRACE
  | LAST
  | LARROW
  | KILL
  | IS
  | IOTA
  | INTERLEAVE
  | INSTANCE
  | INLINE
  | INDUCTIVE
  | INCLUDE
  | IN
  | IMPOSSIBLE
  | IMPORT
  | IMPL
  | IFF
  | IF
  | IDTAC
  | HOARE
  | HINT
  | HAVE
  | HAT
  | GT
  | GOAL
  | GLOB
  | GE
  | FWDS
  | FUSION
  | FUN
  | FROM
  | FORALL
  | FOR
  | FISSION
  | FIRST
  | FINAL
  | FIELD of ([`Raw|`Eq])
  | FEL
  | EXPORT
  | EXPECT
  | EXLIM
  | EXIST
  | EXFALSO
  | EXACT
  | ETA
  | EQUIV
  | EQ
  | EOF
  | END
  | ELSE
  | ELIM
  | ELIF
  | ECALL
  | EAGER
  | DUMP
  | DROP
  | DOTTICK
  | DOTDOT
  | DOT
  | DONE
  | DO
  | DLBRACKET
  | DELTA
  | DECLARE
  | DECIMAL of (EcBigInt.zint * (int * EcBigInt.zint))
  | DEBUG
  | DASHLT
  | CUT
  | CONST
  | CONSEQ
  | CONGR
  | COMMA
  | COLONTILD
  | COLON
  | CLONE
  | CLEAR
  | CLASS
  | CHANGE
  | CFOLD
  | CEQ
  | CBV
  | CASE
  | CALL
  | BYPR
  | BYPHOARE
  | BYEQUIV
  | BY
  | BETA
  | BACKS
  | AXIOMATIZED
  | AXIOM
  | AUTO
  | AT
  | ASYNC
  | ASSUMPTION
  | ASSERT
  | AS
  | APPLY
  | ANDA
  | AND
  | AMP
  | ALIAS
  | ALGNORM
  | ADMITTED
  | ADMIT
  | ABSTRACT
  | ABORT
  | ABBREV

(* This exception is raised by the monolithic API functions. *)

exception Error

(* The monolithic API. *)

val prog: (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (EcParsetree.prog  )

val is_uniop: (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (unit)

val is_numop: (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (unit)

val is_binop: (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (unit)

val global: (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (EcParsetree.global)

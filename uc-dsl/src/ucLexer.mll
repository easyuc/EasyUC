(* OCamlLex specification for UC DSL Lexer (UcLexer module) *)

(* portions of this file are adapted from the EasyCrypt lexer,
   src/ucLexer.mll, which is subject to the following copyright and
   license: *)

(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2018 - Inria
 * Copyright (c) - 2012--2018 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

(* --------------------------------------------------------------------
 * Copyright (c) - 2020 - Boston University
 *
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

(*********************************** Header ***********************************)

(* copied literally into generated UcLexer *)

{
  open Batteries
  open EcUtils
  open UcParser

  module L = EcLocation

  let lex_error lexbuf =
    UcMessage.error_message (L.of_lexbuf lexbuf)

  let _keywords = [
    "Top"             , TOP         ;
    "adversarial"     , ADVERSARIAL ;
    "and"             , ANDTXT      ;
    "direct"          , DIRECT      ;
    "ec_requires"     , EC_REQUIRES ;
    "elif"            , ELIF        ;
    "else"            , ELSE        ;
    "end"             , END         ;
    "envport"         , ENVPORT     ;
    "exists"          , EXIST       ;
    "fail"            , FAIL        ;
    "forall"          , FORALL      ;
    "fun"             , FUN         ;
    "functionality"   , FUNCT       ;
    "if"              , IF          ;
    "implements"      , IMPLEM      ;
    "in"              , IN          ;
    "initial"         , INITIAL     ;
    "intport"         , INTPORT     ;
    "let"             , LET         ;
    "match"           , MATCH       ;
    "message"         , MESSAGE     ;
    "out"             , OUT         ;
    "party"           , PARTY       ;
    "send"            , SEND        ;
    "serves"          , SERVES      ;
    "simulates"       , SIMS        ;
    "simulator"       , SIM         ;
    "state"           , STATE       ;
    "subfun"          , SUBFUN      ;
    "then"            , THEN        ;
    "transition"      , TRANSITION  ;
    "uc_requires"     , UC_REQUIRES ;
    "uses"            , USES        ;
    "var"             , VAR         ;
    "with"            , WITH        ;
  ]

  let keywords =
    let table = Hashtbl.create 0 in
    List.iter (curry (Hashtbl.add table)) _keywords; table

  (* we avoid identifers not allowed by EasyCrypt, because we'll be
     generating EasyCrypt code *)

  let _bad_ec_idents =
    ["Pr"; "abbrev"; "abstract"; "admit"; "algebra"; "alias"; "apply";
    "as"; "assert"; "assumption"; "auto"; "axiom"; "axiomatized";
    "beta"; "by"; "byequiv"; "byphoare"; "bypr"; "call"; "case"; "cbv";
    "cfold"; "change"; "class"; "clear"; "clone"; "congr"; "conseq";
    "const"; "cut"; "debug"; "declare"; "delta"; "do"; "done"; "eager";
    "elim"; "equiv"; "eta"; "exact"; "exfalso"; "export"; "fel";
    "fission"; "for"; "for"; "fusion"; "glob"; "goal"; "have"; "hint";
    "hoare"; "idtac"; "import"; "include"; "inductive"; "inline";
    "instance"; "iota"; "is"; "islossless"; "kill"; "lemma"; "local";
    "logic"; "modpath"; "module"; "move"; "nosmt"; "notation"; "of";
    "op"; "phoare"; "pose"; "pr"; "pragma"; "pred"; "print"; "proc";
    "progress"; "proof"; "prover"; "qed"; "rcondf"; "rcondt"; "realize";
    "reflexivity"; "remove"; "rename"; "replace"; "require"; "res";
    "return"; "rewrite"; "rnd"; "rwnormal"; "search"; "section"; "seq";
    "sim"; "simplify"; "skip"; "smt"; "sp"; "split"; "splitwhile";
    "subst"; "suff"; "swap"; "symmetry"; "theory"; "time"; "timeout";
    "transitivity"; "trivial"; "try"; "type"; "undo"; "unroll"; "while";
    "why3"; "wp"; "zeta"]

  let bad_ec_idents =
    let table = Hashtbl.create 0 in
    List.iter (curry (Hashtbl.add table))
    (List.map (fun x -> (x, ())) _bad_ec_idents);
    table

  let check_bad_ec_ident l id =
    match Hashtbl.find_option bad_ec_idents id with
    | None   -> ()
    | Some _ ->
        lex_error l
        (fun ppf ->
           Format.fprintf ppf
           "@[illegal@ identifer,@ because@ EasyCrypt@ forbids@ it@]")

  (* handling EasyCrypt's operators *)

  (* these are EasyCrypt symbols that are not allowed as infix operators *)

  let ec_non_infix_symbols = ["<<"; ">>"; "<*>"; "<<*>"; "<*>>"]

  (* these are EasyCrypt's "delimiters": *)

  let ec_delimiters =
    [(* the lexer read rule (below) explicitly handles these tokens *)
     ":"; "|"; "/"; "<-"; "->"; "=>";
     (* none of the following are legal UC DSL tokens *)
     "#"; "#|"; "//"; "//#"; "/="; "/#"; "//="; "/>"; "|>";
     "//>"; "||>";  ":="; "<<-"; "->>"]

  (* regular expression that is the disjunction of the delimiters *)

  let ec_delimiters_re =
    let ops = String.join "|" (List.map EcRegexp.quote ec_delimiters) in
    let ops = Printf.sprintf "(%s)" ops in
    EcRegexp.regexp ops

  (* will be called with op consisting of a nonempty sequence of
     opchar's (see below)

     turns op into one of the LOP? tokens (left associative
     operators), using the first character of op to determine the
     precedence level

     if name is used, this will be the argument of the LOP?
     constructor, i.e., the name of the operator *)

  let lop_tok ?name op =
    match op.[0] with
    | '=' | '<' | '>'       -> LOP1 (name |> odfl op)
    | '+' | '-' | '|'       -> LOP2 (name |> odfl op)
    | '*' | '/' | '&' | '%' -> LOP3 (name |> odfl op)
    | _                     -> LOP4 (name |> odfl op)

  (* lex_infix_op will called on a nonempty string of opchar's (see
     below); it will not be called on ":", "|", "/", "->", "<-" and
     "=>" - see read below

     lex_infix_op op will return a token with constructor LOP? or ROP4
     and value op

     if op is a member of ec_non_infix_symbols, then an error message
     is issued, because EasyCrypt won't allow op to be used as an
     infix operator

     otherwise, if op consists of a nonempty sequence of '+'s, this
     results in ROP op

     otherwise, if op consists of a nonempty sequence of '%'s followed
     by a single character, c, then we use lop_tok to produce the
     token, with the argument op set to the string with just c, and
     name set to op, so that c determines the choice of LOP? but op is
     the operator's name

     otherwise, if op has any of EasyCrypt's delimiters as substrings,
     then an error message is issued; this is because the operator couldn't
     be used as an operator in EasyCrypt

     otherwise, lop_tok is called with None and op, so the value of
     the LOP? constructor is op, and the first character of op is used
     to determine the precedence *)

  let lex_infix_op (op : string) lexbuf =
    if List.mem op ec_non_infix_symbols
      then lex_error lexbuf
           (fun ppf ->
              Format.fprintf ppf
              ("@[illegal@ infix@ operator,@ because@ EasyCrypt@ " ^^
               "uses@ it@ for@ another@ purpose@]"))
    else if EcRegexp.match_ (`S "^:+$") op
      then ROP4 op
    else if EcRegexp.match_ (`S "^%+.$") op
      then lop_tok ~name:op (String.of_list [op.[String.length op - 1]])
    else let xs = EcRegexp.split (`C ec_delimiters_re) op in
         match List.find_opt
               (fun x ->
                  match x with
                  | EcRegexp.Delim _ -> true
                  | EcRegexp.Text _  -> false)
               xs with
         | None   -> lop_tok op
         | Some x ->
             match x with
             | EcRegexp.Delim s ->
                 lex_error lexbuf
                 (fun ppf ->
                    Format.fprintf ppf
                    ("@[illegal@ infix@ operator,@ because@ has@ EasyCrypt@ " ^^
                     "delimiter@ as@ substring:@ %s@]")
                    s)
             | EcRegexp.Text _  -> UcMessage.failure "cannot happen"

  (* lex_tick_operator will be called with a nonempty string, op,
     of characters in opchar (see below)

     it uses lop_tok to produce the LOP? token, making "`" ^ op ^ "`"
     be the name of the operator, but using the first character of op
     to determine the precedence level *)

  let lex_tick_operator (op : string) =
    let name = Printf.sprintf "`%s`" op in
    lop_tok ~name op
}

(*********************** Regular Expression Definitions ***********************)

let blank   = [' ' '\t' '\r']
let newline = '\n'
let upper   = ['A'-'Z']
let lower   = ['a'-'z']
let letter  = upper | lower
let digit   = ['0'-'9']

let uint   = digit+

let ichar  = letter | digit | '_' | '\''
let lident = (lower ichar*) | ('_' ichar+)
let uident = upper ichar*
let ident  = lident | uident
let tident = '\'' ident

let _opchar = ['=' '<' '>' '+' '-' '/' '\\' '%' '&' '^' '|' ':' '#' '$']
let opchar  = '*' | _opchar

let sop  = opchar+ | '`' opchar+ '`'
let _sop = _opchar opchar* | '`' opchar+ '`'  (* no initial '*' *)

let nop   = '\\' ichar+
let uniop = nop | ['-' '+']+ | '!'

let binop = sop | nop
let _binop = _sop | nop  (* no initial '*' *)

let numop = '\'' digit+

(******************************** Lexing Rules ********************************)

(* in the generated UcLexer:

val read : Lexing.lexbuf -> UcParser.token *)

rule read = parse
  (* end-of-file *)

  | eof { EOF }

  (* whitespace *)

  | newline { Lexing.new_line lexbuf; read lexbuf }
  | blank+  { read lexbuf }

  (* comments - no other rules match '(', '*', followed by possibly more *)

  | "(*" { comment lexbuf; read lexbuf }
  | "*)" { lex_error lexbuf
           (fun ppf ->
              Format.fprintf ppf
              "@[cannot@ end@ comment@ that@ was@ not@ begun@]") }

  (* fixed length symbols *)

  | '('     { LPAREN     }
  | ')'     { RPAREN     }
  | '{'     { LBRACE     }
  | '}'     { RBRACE     }
  | '['     { LBRACKET   }
  | ']'     { RBRACKET   }
  | ','     { COMMA      }
  | ':'     { COLON      }
  | ";"     { SEMICOLON  }
  | "%"     { PCENT      }
  | "?"     { QUESTION   }
  | "_"     { UNDERSCORE }
  | '.'     { DOT        }
  | '|'     { PIPE       }
  | '@'     { AT         }
  | "~"     { TILD       }
  | "<$"    { LESAMPLE   }
  | "<-"    { LARROW     }
  | "{0,1}" { RBOOL      }
  | ".."    { DOTDOT     }
  | ".["    { DLBRACKET  }
  | ".`"    { DOTTICK    }
  | "<:"    { LTCOLON    }
  | "{|"    { LPBRACE    }
  | "|}"    { RPBRACE    }
  | "`|"    { TICKPIPE   }
  | ":~"    { COLONTILD  }

  (* fixed length used as operators for types and/or expressions, but
     sometimes other uses *)

  | '='     { EQ         }  (* other uses *)
  | "<>"    { NE         }
  | ">"     { GT         }
  | "<"     { LT         }
  | ">="    { GE         }
  | "<="    { LE         }
  | "!"     { NOT        }
  | "^"     { HAT        }
  | "+"     { PLUS       }
  | "-"     { MINUS      }
  | "*"     { STAR       }  (* other uses *)
  | "/"     { SLASH      }
  | "/\\"   { AND        }
  | "&"     { AMP        }
  | "&&"    { ANDA       }
  | "||"    { ORA        }
  | "\\/"   { OR         }
  | "->"    { RARROW     }
  | "=>"    { IMPL       }  (* other uses *)
  | "<=>"   { IFF        }

  (* lower and upper identifers, type identifiers (variables) and
     numeric constants *)

  | lident as id { try Hashtbl.find keywords id with
                   | Not_found ->
                       check_bad_ec_ident lexbuf id; LIDENT id }
  | uident as id { try Hashtbl.find keywords id with
                   | Not_found ->
                       check_bad_ec_ident lexbuf id; UIDENT id }
  | tident as tid { if Char.is_uppercase (tid.[1])
                    then lex_error lexbuf
                         (fun ppf ->
                            Format.fprintf ppf
                            ("@[second character of type variable must " ^^
                             "be lowercase letter@]"))
                    else TIDENT tid }
  | uint          { UINT (EcBigInt.of_string (Lexing.lexeme lexbuf)) }
  | (digit+ as n) '.' (digit+ as f) {
      let nv, fv = EcBigInt.of_string n, EcBigInt.of_string f in
      DECIMAL (nv, (String.length f, fv)) }

  (* strings - used for mixfix operator names *)

  | "\"" {
      let startpos = Lexing.lexeme_start_p lexbuf in
      let str = string (Buffer.create 0) lexbuf in
      lexbuf.lex_start_p <- startpos;
      STRING str }

  (* parenthesized operators *)

  | '(' (_binop as s) blank* ')'       { PBINOP s }  (* avoids comment begin *)
  | '(' blank+ (binop as s) blank* ')' { PBINOP s }  (* avoids comment begin *)
  | '(' blank* (numop as s) blank* ')' { PNUMOP s }
  | '[' blank* (uniop as s) blank* ']' { PUNIOP ("[" ^ s ^ "]") }

  (* operators *)

  | nop as x                           { NOP x }
  | '`' (opchar+ as op) '`'            { lex_tick_operator op }
  | opchar+ as op                      { lex_infix_op op lexbuf }
  | numop as op                        { NUMOP op }

  (* errors *)

  | ['\'' '`'] as c { lex_error lexbuf
                      (fun ppf ->
                         Format.fprintf ppf
                         "@[illegal@ use@ of@ character:@ %c" c) }
  | _               { let s = String.escaped (Lexing.lexeme lexbuf) in
                      lex_error lexbuf
                      (fun ppf ->
                         Format.fprintf ppf
                         "@[unexpected@ character:@ \"%s\"@]" s) }

and comment = parse
  | "*)"    { () }
  | "(*"    { comment lexbuf; comment lexbuf }
  | newline { Lexing.new_line lexbuf; comment lexbuf }
  | eof     { lex_error lexbuf
              (fun ppf ->
                 Format.fprintf ppf
                 "@[unterminated@ comment@ at@ end-of-file@]") }
  | _       { comment lexbuf }

and string buf = parse
  | "\""     { Buffer.contents buf }
  | newline  { lex_error lexbuf
               (fun ppf ->
                  Format.fprintf ppf
                  "@[strings@ may@ not@ contain@ newlines@]") }
  | _ as c   { Buffer.add_char buf c; string buf lexbuf }
  | eof      { lex_error lexbuf
               (fun ppf ->
                  Format.fprintf ppf
                  "@[unterminated@ string@ at@ end-of-file@]") }

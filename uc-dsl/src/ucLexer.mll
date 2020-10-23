(* OCamlLex specification for UC DSL Lexer (UcLexer module) *)

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
    "ec_requires"     , EC_REQUIRES ;
    "uc_requires"     , UC_REQUIRES ;
    "direct"          , DIRECT      ;
    "adversarial"     , ADVERSARIAL ;
    "in"              , IN          ;
    "out"             , OUT         ;
    "message"         , MESSAGE     ;
    "functionality"   , FUNCT       ;
    "implements"      , IMPLEM      ;
    "party"           , PARTY       ;
    "serves"          , SERVES      ;
    "uses"            , USES        ;
    "initial"         , INITIAL     ;
    "state"           , STATE       ;
    "match"           , MATCH       ;
    "fail"            , FAIL        ;
    "send"            , SEND        ;
    "and"             , ANDTXT      ;
    "transition"      , TRANSITION  ;
    "var"             , VAR         ;
    "subfun"          , SUBFUN      ;
    "if"              , IF          ;
    "elif"            , ELIF        ;
    "else"            , ELSE        ;
    "simulator"       , SIM         ;
    "simulates"       , SIMS        ;
    "encode"          , ENCODE      ;
    "decode"          , DECODE      ;
    "as"              , AS          ;
    "with"            , WITH        ;
    "ok"              , OK          ;
    "error"           , ERROR       ;
    "end"             , END         ;
  ]


  let keywords =
    let table = Hashtbl.create 0 in
    List.iter (curry (Hashtbl.add table)) _keywords; table

(*ecLexer operator code BEGIN*)
  let _operators = [
    (":"   , (COLON            , true ));
    ("#"   , (SHARP            , true ));
    ("#|"   ,(SHARPPIPE        , true ));
    ("//"  , (SLASHSLASH       , true ));
    ("//#" , (SLASHSLASHSHARP  , true ));
    ("/="  , (SLASHEQ          , true ));
    ("/#"  , (SLASHSHARP       , true ));
    ("//=" , (SLASHSLASHEQ     , true ));
    ("/>"  , (SLASHGT          , true ));
    ("|>"  , (PIPEGT           , true ));
    ("//>" , (SLASHSLASHGT     , true ));
    ("||>" , (PIPEPIPEGT       , true ));
    ("=>"  , (IMPL             , true ));
    ("|"   , (PIPE             , true ));
    (":="  , (CEQ              , true ));
    ("/"   , (SLASH            , true ));
    ("<-"  , (LARROW           , true ));
    ("->"  , (RARROW           , true ));
    ("<<-" , (LLARROW          , true ));
    ("->>" , (RRARROW          , true ));
    ("!"   , (NOT              , false));
    ("^"   , (HAT              , false));
    ("&"   , (AMP              , false));
    ("&&"  , (ANDA             , false));
    ("/\\" , (AND              , false));
    ("||"  , (ORA              , false));
    ("\\/" , (OR               , false));
    ("<=>" , (IFF              , false));
    ("%"   , (PCENT            , false));
    ("+"   , (PLUS             , false));
    ("-"   , (MINUS            , false));
    ("*"   , (STAR             , false));
    ("<<"  , (BACKS            , false));
    (">>"  , (FWDS             , false));
    ("<:"  , (LTCOLON          , false));
    ("==>" , (LONGARROW        , false));
    ("="   , (EQ               , false));
    ("<>"  , (NE               , false));
    (">"   , (GT               , false));
    ("<"   , (LT               , false));
    (">="  , (GE               , false));
    ("<="  , (LE               , false));
    ("<*>" , (LTSTARGT         , false));
    ("<<*>", (LTLTSTARGT       , false));
    ("<*>>", (LTSTARGTGT       , false));
  ]
  (* ------------------------------------------------------------------ *)
  let operators =
    let table = Hashtbl.create 0 in
    List.iter (curry (Hashtbl.add table)) _operators; table

  let opre =
    let ops = List.map fst (List.filter (snd |- snd) _operators) in
    let ops = List.ksort ~key:(String.length) ~cmp:compare ~rev:true ops in
    let ops = String.join "|" (List.map EcRegexp.quote ops) in
    let ops = Printf.sprintf "(%s)" ops in
    EcRegexp.regexp ops

  (* ----------------------------------------------------------------- *)
  let lex_std_op ?name op =
    match op.[0] with
    | '=' | '<' | '>'       -> LOP1 (name |> odfl op)
    | '+' | '-' | '|'       -> LOP2 (name |> odfl op)
    | '*' | '/' | '&' | '%' -> LOP3 (name |> odfl op)
    | _                     -> LOP4 (name |> odfl op)

  (* ------------------------------------------------------------------ *)
  let lex_operators (op : string) =
    let baseop (op : string) =
      try  fst (Hashtbl.find operators op)
      with Not_found ->
        if   EcRegexp.match_ (`S "^:+$") op
        then ROP4 op else begin
          if   EcRegexp.match_ (`S "^%+.$") op
          then lex_std_op ~name:op (String.make 1 op.[String.length op -1])
          else raise Not_found
        end
    in
      try  [baseop op]
      with Not_found ->
        List.map
        (function
          | EcRegexp.Delim op ->
              fst (Hashtbl.find operators op)
          | EcRegexp.Text op ->
              try baseop op with Not_found -> lex_std_op op)
        (EcRegexp.split (`C opre) op)

  (* ------------------------------------------------------------------ *)
  let lex_tick_operator (op : string) =
    let name = Printf.sprintf "`%s`" op in
    lex_std_op ~name op
(*ecLexer operator code END*)

}

(*********************** Regular Expression Definitions ***********************)

(* regular expression definitions *)

let empty   = ""
let blank   = [' ' '\t' '\r']
let newline = '\n'
let upper   = ['A'-'Z']
let lower   = ['a'-'z']
let letter  = upper | lower
let digit   = ['0'-'9']

let ichar  = letter | digit | '_' | '\''
let ident  = letter ichar* | '_'* letter ichar*

(*ecLexer operator code BEGIN*)
let opchar = ['=' '<' '>' '+' '-' '*' '/' '\\' '%' '&' '^' '|' ':' '#' '$']

let sop = opchar+ | '`' opchar+ '`'
let nop = '\\' ichar+

let uniop = nop | ['-' '+']+ | '!'
let binop = sop | nop
let numop = '\'' digit+
(*ecLexer operator code END*)

(******************************** Lexing Rules ********************************)

(* in the generated UcLexer:

val read     : Lexing.lexbuf -> UcParser.token
val operator : EcUtils.Buffer.t -> Lexing.lexbuf -> EcUtils.Buffer.t
val comment  : Lexing.lexbuf -> unit *)

rule read = parse
  | newline      { Lexing.new_line lexbuf; read lexbuf }
  | blank+       { read lexbuf }
  | ident as id  { try [Hashtbl.find keywords id] with Not_found -> [ID (id)] }
  | "(*" { comment lexbuf; read lexbuf }
  | "*)" { lex_error lexbuf
           (fun ppf ->
              Format.fprintf ppf
              "@[cannot@ end@ comment@ that@ was@ not@ begun@]") }
  (* punctuation *)
  | '('   { [LPAREN]     }
  | ')'   { [RPAREN]     }
  | '{'   { [LBRACE]     }
  | '}'   { [RBRACE]     }
  | ','   { [COMMA]      }
  | ':'   { [COLON]      }
  | ";"   { [SEMICOLON]  }
  | '='   { [EQ]         }
  | '.'   { [DOT]        }
  | '|'   { [PIPE]       }
  | '@'   { [AT]         }
  | "=>"  { [ARROW]      } (*clash with EC operator IMPL*)
  | "!"   { [NOT]        }
  | "<$"  { [ASGSAMPLE]  }
  | "<-"  { [ASGVAL]     } (*clash with EC operator LARROW*)
  | "_"   { [UNDERSCORE] }

(*ecLexer operator code BEGIN*)
  | nop as x { [NOP x] }

  | '`' (opchar+ as op) '`' {
      [lex_tick_operator op]
    }

  | opchar as op {
      let op = operator (Buffer.from_char op) lexbuf in
      lex_operators (Buffer.contents op)
    }

  | numop as op {
      [NUMOP op]
    }
(*ecLexer operator code END*)

  | eof   { [EOF]        }
  | _     { let s = String.escaped (Lexing.lexeme lexbuf) in
            lex_error lexbuf
            (fun ppf ->
               Format.fprintf ppf
               "@[unexpected@ character:@ \"%s\"@]" s) }

(*ecLexer operator code BEGIN*)
and operator buf = parse
  | opchar* as x { Buffer.add_string buf x; buf }
(*ecLexer operator code END*)

and comment = parse
  | "*)"    { () }
  | "(*"    { comment lexbuf; comment lexbuf }
  | newline { Lexing.new_line lexbuf; comment lexbuf }
  | eof     { lex_error lexbuf
              (fun ppf ->
                 Format.fprintf ppf
                 "@[unterminated@ comment@ at@ end-of-file@]") }
  | _       { comment lexbuf }

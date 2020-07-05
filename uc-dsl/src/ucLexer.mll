(*stuff copied from 
http://www.cs.cornell.edu/courses/cs3110/2015fa/l/12-interp/rec.html
and
https://v1.realworldocaml.org/v1/en/html/parsing-with-ocamllex-and-menhir.html
and (mostly)
ecLexer.mll
*)
(* The first section of the lexer definition, called the *header*,
   is the part that appears below between { and }.  It is code
   that will simply be copied literally into the generated lexer.ml. *)

{
  open UcParser
  open EcUtils
  module L  = EcLocation
  exception LexicalError of L.t option * string

  let unterminated_comment () =
    raise (LexicalError (None, "unterminated comment"))

  let lex_error lexbuf msg =
    raise (LexicalError (Some (L.of_lexbuf lexbuf), msg))

  let _keywords = [                     
    "direct"        , DIRIO      ;
    "adversarial"   , ADVIO      ;
    "in"              , IN         ;
    "out"             , OUT        ;
    "message"         , MESSAGE    ;
    "functionality"   , FUNCT      ;
    "implements"      , IMPLEM     ;
    "party"           , PARTY      ;
    "serves"          , SERVES     ;
    "uses"            , USES       ;
    "initial"         , INITIAL    ;
    "state"           , STATE      ;
    "match"           , MATCH      ;
    "othermsg"        , OTHERMSG   ;
    "fail"            , FAIL       ;
    "send"            , SEND       ;
    "and"             , ANDTXT     ;
    "transition"      , TRANSITION ;
    "requires"        , REQUIRES   ;
    "var"             , VAR        ;
    "subfun"          , SUBFUN     ;
    "if"              , IF         ;
    "elif"            , ELIF       ;
    "else"            , ELSE       ;
    "simulator"       , SIM        ;
    "simulates"       , SIMS       ;
    "encode"          , ENCODE     ;
    "decode"          , DECODE     ;
    "as"              , AS         ;
    "with"            , WITH       ;
    "ok"              , OK         ;
    "error"           , ERROR      ;
    "end"             , END        ;
  ]

  let _operators = [
    ("^"   , HAT );
    ("/\\" , AND );
    ("\\/" , OR  );
    ("="   , EQ  );
    ("*"   , STAR);
  ]

  let operators =
    let table = Hashtbl.create 0 in
    List.iter (curry (Hashtbl.add table)) _operators; table

  let keywords =
    let table = Hashtbl.create 0 in
    List.iter (curry (Hashtbl.add table)) _keywords; table

  let lex_operators (op : string) =
    try  Hashtbl.find operators op
    with Not_found -> ROP4 op
	

}


(* The second section of the lexer definition defines *identifiers*
   that will be used later in the definition.  Each identifier is
   a *regular expression*. *)

let empty   = ""
let blank   = [' ' '\t' '\r']
let newline = '\n'
let upper   = ['A'-'Z']
let lower   = ['a'-'z']
let letter  = upper | lower
let digit   = ['0'-'9']

let jchar  = (letter | digit | '_' | '\'')
let ident  = (letter jchar*| '_'* letter jchar*)

  (* ------------------------------------------------------------------ *)

let opchar = ['=' '/' '\\' '^' '*']

let sop = opchar+ 

let binop = sop 

  (* ------------------------------------------------------------------ *)

(* The final section of the lexer definition defines how to parse a character
   stream into a token stream.  Each of the rules below has the form 
     | regexp { action }
   If the lexer sees the regular expression [regexp], it produces the token 
   specified by the [action].  We won't go into details on how the actions
   work.  *)
(* -------------------------------------------------------------------- *)
rule read = parse
  | newline      { Lexing.new_line lexbuf; read lexbuf }
  | blank+       { read lexbuf }
  | ident as id  { try Hashtbl.find keywords id with Not_found -> ID (id) }
  | "(*" { comment lexbuf; read lexbuf }
  (* punctuation *)
  | '('   { LPAREN     }
  | ')'   { RPAREN     }
  | '{'   { LBRACE     }
  | '}'   { RBRACE     }
  | ','   { COMMA      }
  | ':'   { COLON      }
  | ";"   { SEMICOLON  }
  | '='   { EQ         }
  | '.'   { DOT        }
  | '|'   { PIPE       }
  | '@'   { AT         }
  | "=>"  { ARROW      }
  | "!"   { NOT        }
  | "<$"  { ASGSAMPLE  }
  | "<-"  { ASGVAL     }
  | "_"   { UNDERSCORE }
  (*operators*)
  | opchar as op {
      let op = operator (Buffer.from_char op) lexbuf in
      lex_operators (Buffer.contents op)
    }

  | eof   { EOF        }
  | _     { lex_error lexbuf "invalid character"}

and operator buf = parse
  | opchar* as x { Buffer.add_string buf x; buf }

and comment = parse
  | "*)"        { () }
  | "(*"        { comment lexbuf; comment lexbuf }
  | newline     { Lexing.new_line lexbuf; comment lexbuf }
  | eof         { unterminated_comment () }
  | _           { comment lexbuf }

(* And that's the end of the lexer definition. *)

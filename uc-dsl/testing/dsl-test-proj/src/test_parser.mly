%{
    open Test_types
%}

%token EOF
%token <string> DESC
%token <string list> ARGS
%token  <Test_types.outcome * string> OUT

%start <Test_types.expr list> prog

%%

(* The lexer returns token of form stmt; EOF 
stmt is a list of expressions, hence each statement looks like
expressions :: statement
expressions are of 3 types as defined below *)

prog:
  | e = stmt ; EOF {e }
  ;

stmt:
  |e1 = expr {[e1] }
  |e1 = expr ; l = stmt { e1 :: l }

expr:
  | d = DESC   { Desc d}
  | o = ARGS  {Args o}
  | o = OUT {Outcome (fst o, snd o)}
  ;




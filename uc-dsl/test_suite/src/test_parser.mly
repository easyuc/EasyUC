%{
    open Test_types
%}

%token EOF
%token <string> REQ
%token <string> DESC
%token <string list> ARGS
%token  <Test_types.outcome * string> OUT

%start <Test_types.expr list> prog

%%

prog:
  | e = stmt ; EOF { e (* let _ = print_string "I am in parse prog line e = stmt " in e *)}
  ;

stmt:
  |e1 = expr {[e1] (*  let _ = print_string "I am in parse stmt line 1 \n" in [e1] *) }
  |e1 = expr ; l = stmt {(* let _ = print_string "I am in parse stmt line 2 \n" in*) e1 :: l }

expr:
  | d = DESC   {(*print_string "\n We are at DESC Level in Parser\n";*) Desc d}
  | o = ARGS  {(*print_string "\n We are at OPT level in Parser \n";*) Args o}
  | o = OUT {(*print_string "\n We are at Outcome level in Parser \n"; *)Outcome (fst o, snd o)}
  | r = REQ {Requires r}
  ;




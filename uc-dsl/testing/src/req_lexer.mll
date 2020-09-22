{
open Test_parser
open Test_types
open Str
open Lexing

exception SyntaxError of string

let next_line lexbuf = let pos = lexbuf.lex_curr_p in
    	      	       lexbuf.lex_curr_p <- {
		       	pos with pos_bol = lexbuf.lex_curr_pos; pos_lnum = pos.pos_lnum + 1
			}

let error_raise s1 s2 lexbuf=
    let p = Lexing.lexeme_start_p lexbuf in
    let line_num = p.Lexing.pos_lnum in
    raise (SyntaxError ((s1^" at line ")^ string_of_int(line_num)^" "^s2))
}

let alphanum = ['0'-'9' '_' 'a'-'z' 'A'-'Z']
let alpha = ['a'-'z' 'A'-'Z']+

rule my_lexer = parse
     	|[' ' '\t' '\r']+	{my_lexer  lexbuf }
	|"(*"			{comments 0 lexbuf; my_lexer lexbuf }
	|eof			{EOF }
	|'\n'			{my_lexer lexbuf} 
	|"ec_requires"		{req_ec_comments lexbuf}
	|"uc_required"		{req_uc_comments lexbuf}
	|_ 			{my_lexer lexbuf }
					
and comments level = parse
    	|"*)"			{if level = 0 then ()
		  		   else comments (level-1) lexbuf
				   }
	|"(*"  			{comments (level+1) lexbuf	}
	|'\n'			{next_line lexbuf; comments level lexbuf}
	|_ 			{comments level lexbuf }
	|eof			{error_raise "Unexpected end of file" "" lexbuf }
	
and req_ec_comments = parse
    	|[' ' '\t' '\r']+	{req_ec_comments lexbuf }
	|['\n']     		{req_ec_comments lexbuf }
	|"(*"  			{comments 0 lexbuf; req_ec_comments lexbuf }
	|alpha alphanum* as ste	{REQ (req ste lexbuf^".ec")}
	|eof			{error_raise " Unexpected end of file " "" lexbuf }

and req_uc_comments = parse
    	|[' ' '\t' '\r']+	{req_uc_comments lexbuf }
	|['\n']     		{req_uc_comments lexbuf }
	|"(*"  			{comments 0 lexbuf; req_uc_comments lexbuf }
	|alpha alphanum* as ste	{REQ (req ste lexbuf^".uc")}
	|eof			{error_raise " Unexpected end of file " "" lexbuf }

and req s = parse
	|"."			{s}
	|alpha alphanum*	{req (s ^ (Lexing.lexeme lexbuf)) lexbuf}
	|eof			{error_raise "Unexpected end" "" lexbuf}
	|_			{error_raise "Unexpected character" "" lexbuf}


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

let line = [^ '\n']* ['\n']
let id = [^ '\n' ' ' '\t']+
let alphanum = ['0'-'9' '_' 'a'-'z' 'A'-'Z' '.']
let alpha = ['a'-'z' 'A'-'Z' '.']+
let file = ['a'-'z' 'A'-'Z'  '-' '0'-'9' '.' '_']

rule my_lexer = parse
     	|[' ' '\t' '\r']+	{my_lexer  lexbuf }
	|"(*"			{comments 0 lexbuf; my_lexer lexbuf }
	|eof			{EOF }
	|'\n'			{next_line lexbuf;  my_lexer lexbuf} 
	|"description"		{desc_comments lexbuf}
	|"args"			{args lexbuf }
	|"outcome"		{outcome lexbuf }
	|_ 			{error_raise "Something went wrong"
				 (Lexing.lexeme lexbuf) lexbuf}
					
and comments level = parse
    	|"*)"			{if level = 0 then ()
		  		   else comments (level-1) lexbuf
				   }
	|"(*"  			{comments (level+1) lexbuf	}
	|'\n'			{next_line lexbuf; comments level lexbuf}
	|_ 			{comments level lexbuf }
	|eof			{error_raise "Unexpected end of file" "" lexbuf }
	
and desc_comments = parse
    	|[' ' '\t' '\r']+	{desc_comments lexbuf }
	|['\n']     		{next_line lexbuf; DESC (desc "" lexbuf) }
	|"(*"  			{comments 0 lexbuf; desc_comments lexbuf }
	|_ 			{error_raise "Text should start in a new line" "" lexbuf}
	|eof			{error_raise " Unexpected end of file " "" lexbuf }

and desc s = parse
	|".\n"			{new_line lexbuf; s }
	|line			{next_line lexbuf; desc (s ^ (Lexing.lexeme lexbuf)) lexbuf}
	|eof			{error_raise "Unexpected end of file" "" lexbuf }

and args = parse
    	|[' ' '\t''\r']+		{args lexbuf }
	|['\n']			{next_line lexbuf; args lexbuf}
	|"(*"			{comments 0 lexbuf; args lexbuf}
	|":"			{args_parse [] lexbuf}
	|_			{error_raise " : expected " "" lexbuf }
	
and args_parse s1 = parse
    	|[' ' '\t']+		{args_parse s1 lexbuf}
	|"(*" 			{comments 0 lexbuf; args_parse s1 lexbuf}
	|'\n' 	    	       	{next_line lexbuf;  ARGS s1}
	|"-" alpha alphanum* as str	{args_parse (s1@[str]) lexbuf}
	|alpha alphanum* as str	        {args_parse (s1@[str]) lexbuf}
	|file+ as str	 	        {args_parse (s1@[str]) lexbuf}
	|_     		        {error_raise "Unexpected character in args "
				(Lexing.lexeme lexbuf) lexbuf }
	|eof			{error_raise "Unexptected end of file " "" lexbuf}


and outcome = parse
    	|[' ' '\t']		{outcome lexbuf }
	|['\n']			{next_line lexbuf; outcome lexbuf}
	|"(*"			{comments 0 lexbuf; outcome lexbuf}
	|":"			{out_parse Success false lexbuf}
	|_			{error_raise " : expected" "" lexbuf}
	
and out_parse o1 bool = parse
    	|[' ' '\t' '\r']+		{out_parse o1 bool lexbuf}
	|['\n']			{if bool = false
				    then error_raise "success/failure expected" "" lexbuf
	     			    else next_line lexbuf ; OUT (o1, desc "" lexbuf)}
	|"(*" 			{comments 0 lexbuf; out_parse o1 bool lexbuf }
	|"success" 		{if bool = false then
				 let o1 = Success in out_parse o1 true lexbuf
				 else
				 error_raise ((Lexing.lexeme lexbuf) ^ " is redundant") "" lexbuf
				}
	|"failure"		{if bool = false then
				  let o1= Failure in out_parse o1 true lexbuf
				 else
				  error_raise "" ((Lexing.lexeme lexbuf)^" is redundant") lexbuf }
	|_			{error_raise "" "Syntax is outcome: succes/failure \n ... \n.\n " lexbuf}	


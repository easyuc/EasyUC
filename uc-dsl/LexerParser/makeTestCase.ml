open DlLexer
open DlParseTree
open DlParseFile
open EcLocation

let string_of_location (loc:EcLocation.t) : string = 
	"{ loc_fname=\""^loc.loc_fname^
	"\";loc_start=("^(string_of_int(fst loc.loc_start))^","^(string_of_int(snd loc.loc_start))^
	"); loc_end=("^(string_of_int(fst loc.loc_end))^","^(string_of_int(snd loc.loc_end))^
	"); loc_bchar="^(string_of_int loc.loc_bchar)^
	"; loc_echar="^(string_of_int loc.loc_echar)^"}"

let string_of_msg msg : string = 
	match msg with
	| Some s -> "(Some \""^s^"\")"
	| None -> "None"

let string_of_ParseError (loc,msg) : string =
	"ParseError (\n"^(string_of_location loc)^",\n"^(string_of_msg msg)^")"

let string_of_ParseError2 (loc1,loc2,msg) : string =
	"ParseError2 (\n"^(string_of_location loc1)^",\n"^(string_of_location loc2)^",\n\""^msg^"\")"

let string_of_loco loco : string =
	match loco with
	| Some loc -> "(Some "^(string_of_location loc)^")"
	| None -> "None"

let string_of_LexicalError (loco,msg) : string =
	"LexicalError (\n"^(string_of_loco loco)^",\n\""^msg^"\")"

let string_of_test dlFile =
	let filename = "./tests/"^dlFile^".uc" in
	print_string ("let "^dlFile^" = \n{\n\tfilename = \""^filename^"\";\n\texpectedResult = ");
	(	
	try
	  parse_file filename;
	  print_string "None"
	with
	  | ParseError(loc, msg) -> print_string ("Some ("^(string_of_ParseError(loc, msg))^")")
	  | ParseError2(loc1, loc2, msg) -> print_string ("Some ("^(string_of_ParseError2(loc1, loc2, msg))^")")
	  | LexicalError(loco,msg) -> print_string ("Some ("^(string_of_LexicalError(loco,msg))^")")
	);
	print_string "\n}\n\n"

let run = string_of_test Sys.argv.(1)

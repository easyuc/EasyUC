(* test_main.ml *)

open Test_types
open Str
open Printf
open Unix
   
(* print_expr together with print_list displays the content of a TEST file.
	This comes into the picture with DEBUG option *)
   
let print_expr (e:expr) =
  match e with
  |Desc d -> print_string ("Description\n"^ d ^"\nEnd of description\n")
  |Args o -> print_endline "ARGS";
	     List.iter print_endline o ;
	     print_endline "End of ARGS"
  |Outcome (o1,o2) -> let _ = print_endline "OUTCOME" in
	              let _ = if o1=Success then print_endline "Success"
	                      else if o1=Failure then print_endline "Failure"
	                      else print_endline "Unknown"
	              in let _ = print_endline "Outcome description" in
	                 print_string o2;
	                 print_endline "____End of outcome description____"
	                 
let print_list lst =
  let rec print_elements er args = function
    |[] -> (*print_string "______END______\n";*) args
    |e::l -> match e with
	     |Args o -> print_expr e; print_elements er (o@args) l
	     |Outcome (o1, o2) -> if er <> 0 then
	                            (print_endline "ERROR: Multiple outcomes";
	                             print_expr e;
	                             print_elements (er+1) args l)
	                          else
	                            (print_expr e;
	                             print_elements (er+1) args l)
	     |_ -> print_expr e; print_elements er args l
  in
  let arg_list = print_elements 0 [] lst in
  match arg_list with
  |[] -> print_endline "Warning: Empty arguments"
  |_ -> ()
      
(* get_desc is used in verbose mode to get desc of the TEST file *)
      
let get_desc lst =
  let rec desc lst_d str =
    match lst_d with
    |[] -> str
    |e::l -> match e with
	     |Desc d -> desc l str^d
	     |_ -> desc l str
  in desc lst ""
   
   
let read_file filename =
  let file = open_in filename in
  let s = really_input_string file (in_channel_length file) in
  close_in file;
  s 

(* I am not sure where I learned this code from
parse takes a file, and uses above read_file to convert it into
a string s, now we use Lexing to convert it into lexbuf and we use
our test_parser and test_lexer to generate token and then parse the
file *)  
  
let parse (file_name : string) =
  let s = read_file(file_name) in
  let lexbuf = Lexing.from_string s in
  let ctr = 
    try Test_parser.prog Test_lexer.my_lexer lexbuf
    with Parsing.Parse_error ->
      let p = Lexing.lexeme_start_p lexbuf in
      Printf.eprintf "\nParse error at line %d character %d near %s \n"
	p.Lexing.pos_lnum
	(p.Lexing.pos_cnum - p.Lexing.pos_bol)
	(Lexing.lexeme lexbuf);
      failwith "Syntax error" in
  ctr
  
(* The acceptable content of a director are
	| TEST file + contents + optional sub directories
	| If a TEST file is found, subfolders will be ignored
	| Files with names starting with "readme" only + optional sub directories
                (readme is case insenstive)
	| Only sub folders will be searched for TEST files/tests
	| No files but sub directories
	| All subdirectories will be searched for TEST files/tests
	| Any others will be ignored
        | log file
	
 *)
  
let rec walk_directory_tree dir (test_list:string list) (er_string:string) =
  try
    let contents = Array.to_list (Sys.readdir dir) in
    let dirs, files =
      List.fold_left (fun (dirs,files) f ->
	  match (stat (dir^"/"^f)).st_kind with
	  | S_REG -> if (String.sub f 0 1 = ".") then
	               (dirs, files) (* f is Hidden file *)
	             else (dirs, f::files)
	  | S_DIR -> (f::dirs, files) (* Directory *)
	  | _ -> (dirs, files)
	) ([],[]) contents
    in
    let dirs = List.rev_map (Filename.concat dir) dirs in
    if (List.mem ("TEST") files) then
      (test_list @ [dir^"/TEST"], er_string)
    else if (List.length files = 0 && List.length dirs = 0) then
      (test_list, er_string)
    else if
      ((List.length files = 0 && List.length dirs <> 0) ||
	 (List.for_all
	    (fun x ->
              (if (String.length(x) >= 6) then
                 (String.lowercase_ascii (String.sub x 0 6) = "readme")
               else
                 (x = "log"))) files ))
    then
      (let rec walk_folders f_list t_list e_string =
	 match f_list with
	 |[] -> (t_list, e_string)
	 |e::l -> let (t_list_new, e_string_new) =
	            walk_directory_tree e t_list er_string in
	          walk_folders l t_list_new (e_string^e_string_new)
       in
       walk_folders dirs test_list er_string)
    else
      (test_list,(er_string^"\n"^
	            "Error:Unexpected files found in the directory:"
	            ^dir
	            ^"\nDirectory ignored, please clean files\n"))
  with
  |Sys_error e -> ( test_list , er_string^"\nError: "^ e)
  |Unix_error (_,_,e) -> (test_list , er_string^"\nError:"^ e)
  |_ -> (test_list , er_string^"\nSome unknown error occured")
      
  
(* The below code is originally written by Alley and slightly modified here, 
	which executes a command together with a list of options and return
	output or error *)
  
let () = Printexc.record_backtrace true
       
let read_to_eof ch =
  let rec reads xs =
    match try Some (input_line ch) with
	    End_of_file -> None with
      None -> String.concat "" (List.rev xs)
    | Some x -> reads ((x ^ "\n") :: xs)
  in reads []
   
let norm_stat stat =
  match stat with
    Unix.WEXITED n -> Some n
  | _ -> None
       
let run folder (f_name: string array) =
  (* pipe for feeding child process's standard output to parent *)
  let (pipe_in, pipe_out) = Unix.pipe () in
  match Unix.fork () with
  | 0 -> (* child process *)
     Unix.close pipe_in;
     (* send both stdout and stderr into the pipe *)
     Unix.dup2 pipe_out Unix.stdout;
     Unix.dup2 pipe_out Unix.stderr;
     Unix.close pipe_out;
     Unix.chdir folder;
     Unix.execvp (Array.get f_name 0) f_name
  | _ -> (* parent (original) process *)
     Unix.close pipe_out;
     let out_in = Unix.in_channel_of_descr pipe_in in
     let s_out = read_to_eof out_in in
     let () = close_in out_in in
     let (_, stat) = Unix.wait() in
     (norm_stat stat, s_out) 

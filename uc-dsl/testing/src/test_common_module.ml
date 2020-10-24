(* test_common_module.ml *)

open Test_types
open Str
open Printf
open Unix
   
(* print_expr together with print_list displays the content of a TEST file.
	This comes into the picture with DEBUG option *)
   
let print_expr (e:expr) =
  match e with
  |Desc d -> print_string ("__description__\n"^ d ^"__end of description__\n")
  |Args o -> print_endline "__args__";
	     List.iter print_endline o ;
	     print_endline "__end of ARGS__"
  |Outcome (o1,o2) -> let _ = print_endline "__outcome__" in
	              let _ = if o1=Success then print_endline "success"
	                      else if o1=Failure then print_endline "failure"
	                      else print_endline "Unknown"
	              in let _ = print_endline "__outcome description__" in
	                 print_string o2;
	                 print_endline "____end of outcome description____"
	                 
let print_list lst =
  let rec print_elements er args = function
    |[] ->  (args, er)
    |e::l -> match e with
	     |Args o -> print_expr e; print_elements er (o@args) l
	     |Outcome (o1, o2) -> print_expr e;
                                  print_elements (er+1) args l
	     |_ -> print_expr e; print_elements er args l
  in
  let (arg_list, er_num) = print_elements 0 [] lst in
  let _ =
    match arg_list with
    |[] -> print_endline "Error: Empty arguments"
    |_ -> ()
  in if er_num = 0 then
       print_endline "Error: Outcome missing"
     else if er_num > 1 then
       print_endline "Error: Multiple outcomes"

(* check_ec_standard checkes .uc anc .ec files for naming standard.
The file name shoudl start with a letter and can contain numbers and a '_' *)
   
     
let check_ec_standard file  =
  let id = Str.regexp
             "[a-z A-Z]+[a-z 0-9 A-Z]*_?[a-z 0-9 A-Z]*\\.\\(uc\\|ec\\)$" in
 if (Str.string_match id file 0 = false) then
   "Warning: "^file ^ " file doesn't match EC naming standard \n"
 else ""

 
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
  let lexbuf = Lexing.from_channel (open_in file_name) in
  let ctr = 
    Test_parser.prog Test_lexer.my_lexer lexbuf
(*    with Parsing.Parse_error ->
      let p = Lexing.lexeme_start_p lexbuf in
      Printf.eprintf "\nParse error at line %d character %d near %s \n"
	p.Lexing.pos_lnum
	(p.Lexing.pos_cnum - p.Lexing.pos_bol)
	(Lexing.lexeme lexbuf); *)
       in
       ctr    
  
(* The acceptable content of a director are
	| TEST file + contents + optional sub directories
	| If a TEST file is found, subfolders will be ignored
	| Files with names starting with "readme" only + 
                                    optional sub directories
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
      (let dir_content  = List.filter (fun x -> (x <> "TEST" && x <> "log") ||
                  (String.lowercase_ascii (String.sub x 0 6) = "readme")) files
       in
       let file_list = match dir_content with
         |[] -> ""
         |e::l -> e
       in
      (test_list,(er_string^"\n"^
	            "Error:Unexpected files found in the directory:"
	            ^dir^"\nFor example:\n"^dir^"/"^file_list
	            ^"\nDirectory ignored, please clean files\n")))
  with
  |Sys_error e -> ( test_list , er_string^"\nError:"^ e)
  |Unix_error (_,_,e) -> (test_list , er_string^"\nError:"^ e)
  |_ -> (test_list , er_string^"\nSome unknown error occured"^
        "please report this as a bug")
      
  
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

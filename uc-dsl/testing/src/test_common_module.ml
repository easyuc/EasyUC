(* test_common_module.ml *)

open Test_types
open Str
open Printf
open Unix

exception Error of string
                 
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
	              in
                           if o2 <>"" then
                             (print_endline "__outcome description__";
                              print_string o2;
                              print_endline "__end of outcome description__")
                           else
                             print_endline "Warning: description missing"
                           
	                 
let print_list lst =
  let rec print_elements = function
    |[] -> ()
    |e::l -> (print_expr e; print_elements l)
  in
  print_elements lst

let check_fields lst = 
    let rec check arg desc out = function
      |[] -> (arg, desc, out)
      |e::l -> match e with
               |Args o -> check (arg+1) desc out l
               |Desc d -> check arg (desc+1) out l
               |Outcome (o1,o2) -> check arg desc (out+1) l
    in
    let (arg_1, desc_1, out_1) = check 0 0 0 lst in
    let s1 = 
    if arg_1 <> 1 then
      (if arg_1 = 0 then "Error: Missing Args"
       else "Error: Multiple Args")
    else ""
    in let s2 = 
     if desc_1 <> 1 then
      (if desc_1 > 1 then "Warning: Multiple Descriptions"
       else "Warning: Description missing")
     else ""
     in let s3 = 
    if out_1 <> 1 then
      (if out_1 = 0 then "Error: Outcome is missing"
       else "Error: Multiple Outcomes")
    else ""
        in
        if s3 <> "" then
          (if s1 <> "" then (s1^"\n"^s3 , s2)
           else (s3, s2))
        else (s1, s2)
                       
(* check_ec_standard checkes .uc anc .ec files for naming standard.
The file name shoudl start with a letter and can contain numbers and a '_' *)
     
     
let check_ec_standard file  =
  let id =
    Str.regexp "[a-z A-Z]+[a-z 0-9 A-Z]*_?[a-z 0-9 A-Z]*\\.\\(uc\\|ec\\)$" in
  if (Str.string_match id file 0 = false) then
    "\nWarning: "^file ^ " file doesn't match EC naming standard"
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
  
let parse (file_name : string) =
  let ch = open_in file_name in
  let lexbuf = Lexing.from_channel ch in
  try
    let ctr = 
      Test_parser.prog Test_lexer.my_lexer lexbuf in
    close_in ch;
    ctr
  with
  |e -> close_in ch; raise e    
  
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
      (let dir_content  =
         List.filter (fun x -> (x <> "TEST" && x <> "log") ||
                                 (String.lowercase_ascii
                                    (String.sub x 0 6) = "readme")) files
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

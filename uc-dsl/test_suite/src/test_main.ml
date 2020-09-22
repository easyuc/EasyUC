(* test_main.ml *)

open Test_types
open Test_log
open Str
open Printf
open Unix
   
let print_expr (e:expr) =
  match e with
  |Requires r -> print_endline "Requires"; print_endline r; print_endline "End of Requires"
  |Desc d -> print_endline "Description"; print_string d; print_endline "End of description"
  |Args o -> print_endline "ARGS"; List.iter print_endline o ; print_endline "End of ARGS"
  |Outcome (o1,o2) -> let _ = print_endline "OUTCOME" in
                      let _ = if o1=Success then print_endline "Success"
                      else if o1=Failure then print_endline "Failure"
                              else print_endline "Unknown"
                      in let _ = print_endline "Outcome description" in
                         print_string o2;
                         print_endline "____End of outcome description____"
                              
let get_desc lst =
  let rec desc lst_d str =
    match lst_d with
    |[] -> str
    |e::l -> match e with
             |Desc d -> desc l str^d
             |_ -> desc l str
  in desc lst ""
                         
let print_list lst =
  let rec print_elements er args = function
    |[] -> (*print_string "______END______\n";*) args
    |e::l -> match e with
                |Args o -> print_expr e; print_elements er (o@args) l
                |Outcome (o1, o2) ->  if er <> 0 then
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

let read_file filename =
  let file = open_in filename in
  let s = really_input_string file (in_channel_length file)  in
  close_in file;
  s 

let parse (file_name : string) =
  let s = read_file(file_name) in
  let lexbuf = Lexing.from_string s in
  (*let _ = Printf.printf "Input string is @%s\n" (Bytes.to_string (lexbuf.lex_buffer)) in*)
  let ctr = 
    try  Test_parser.prog Test_lexer.my_lexer lexbuf
    with Parsing.Parse_error ->
      let p = Lexing.lexeme_start_p lexbuf in
      Printf.eprintf "\nParse error at line %d character %d near %s \n"
	p.Lexing.pos_lnum
	(p.Lexing.pos_cnum - p.Lexing.pos_bol)
	(Lexing.lexeme lexbuf);
      failwith "Syntax error" in
  ctr
  
             
let walk_directory_tree dir pattern =
  let re =  Str.regexp pattern in
  (* pre-compile the regexp *)
  let select str = Str.string_match re str 0 in
  let rec walk acc er_string  = function
    | [] -> (acc, er_string )
    | dir::tail ->
       try
         let contents = Array.to_list (Sys.readdir dir) in
         let contents = List.rev_map (Filename.concat dir) contents in
         let dirs, files =
           List.fold_left (fun (dirs,files) f ->
               match (stat f).st_kind with
               | S_REG -> (dirs, f::files)  (* Regular file *)
               | S_DIR -> (f::dirs, files)  (* Directory *)
               | _ -> (dirs, files)
             ) ([],[]) contents    
         in
         let matched = List.filter (select) files in
         walk ( matched @ acc) er_string (dirs @ tail)
       with
       |Sys_error e -> walk (acc) (er_string^"\n"^ e) (tail)
       |Unix_error (_,_,e) -> walk (acc) (er_string^"\n"^ e) (tail)
       |_ -> walk (acc) (er_string^"\nsomeunknown error occured") (tail)
  in
  walk [] "" [dir]


let () = Printexc.record_backtrace true

let read_to_eof ch =
  let rec reads xs =
    match try Some (input_line ch) with
            End_of_file -> None with
      None   -> String.concat "" (List.rev xs)
    | Some x -> reads ((x ^ "\n") :: xs)
  in reads []

let norm_stat stat =
  match stat with
    Unix.WEXITED n -> Some n
  | _              -> None

let run folder (f_name: string array) =
  (*    pipe for feeding child process's standard output to parent *)
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
   | _ ->  (* parent (original) process *)
      Unix.close pipe_out;
      let out_in = Unix.in_channel_of_descr pipe_in in
      let s_out = read_to_eof out_in in
      let () = close_in out_in in
      let (_, stat) = Unix.wait() in
      (norm_stat stat, s_out)    

(* test_run_tests.ml *)
open Test_types
open Test_common_module
open Test_log
   
   
let verbose = ref false
let debug = ref false
let quiet = ref false

(* The above 3 variables refer to the options as their name suggests *)


let log_str = ref ""
let sec_str = ref ""
let desc_str = ref ""
            
(* check_ec_standard checkes .uc anc .ec files for naming standard.
The file name shoudl start with a letter and can contain numbers and a '_' *)
   
let check_ec_standard file  =
  let id = Str.regexp
             "[a-z A-Z]+[a-z 0-9 A-Z]*_?[a-z 0-9 A-Z]*\\.\\(uc\\|ec\\)$" in
 if (Str.string_match id file 0 = false) then
   log_str := "Warning: "^file ^ " file doesn't match EC naming standard \n"

  
(* check_name contents sees if there any .ec or .uc files in the directory 
if yes then their names will be passed onto check_ec_standard *)
  
let check_name contents  =
  let rec check file_list  =
    match file_list with
    |[] -> ()
    |e::l -> let len = String.length e in
             let _ = if ((len >= 4) &&
                             ( String.sub e (len -3) 3 = ".uc" ||
                                 String.sub e (len -3) 3 =  ".ec"))
                        then check_ec_standard e
                 in check l
  in check contents
   
(* dir_name takes a file, gets it's directory by using 
Filename.dirname so that the contents can be examined by check_name function *)
 
let dir_name file =
  let dir = Filename.dirname file in
  let contents = Array.to_list (Sys.readdir dir) in
  check_name contents
      
let read_file filename =
  let file = open_in filename in
  let s = really_input_string file (in_channel_length file) in
  close_in file; (*;printf "I am at read file";*)
  s 

let parse (file_name : string) =
  let s = read_file(file_name) in
  let lexbuf = Lexing.from_string s in
  let ctr = 
    try  Test_parser.prog Test_lexer.my_lexer lexbuf
    with Parsing.Parse_error ->
      let p = Lexing.lexeme_start_p lexbuf in
      Printf.eprintf "\nParse error at line %d character %d near %s \n"
	p.Lexing.pos_lnum
	(p.Lexing.pos_cnum - p.Lexing.pos_bol)
	(Lexing.lexeme lexbuf);
      failwith "Syntax erroor" in
  ctr

let rec last_element y list = 
  match list with 
  | [] -> failwith "List is empty"
  | [x] -> if y=[| |] then [|x|] else Array.append y [|x|]
  | first_el::rest_of_list -> let z = Array.append y [|first_el|] in
                              last_element z rest_of_list
                                                                   
let rec match_expr expression f_name out_come1 out_come2 number =
  match expression with
  |[] -> if f_name = [| |] then failwith " Empty args "
         else if number = 0 then failwith " Outcome missing "
         else
           if out_come1 = Empty then
             failwith "Outcome has to be succes or failure"
           else (f_name, out_come1, out_come2)
(* outcome can be Empty in addition to success and failure
this has been instroduced for programming convinience *)
  |e::l -> match e with
           |Args o -> let f_array = last_element [| |] o in
                      match_expr l f_array out_come1 out_come2 number
           |Outcome (o1, o2) -> if number = 0 then
                                  match_expr l f_name o1 o2 (number+1)
                                else
                                  failwith "Multiple outcomes are not allowed"
           |_ -> match_expr l f_name out_come1 out_come2 number

(* create_conflict has 3 arguments file - this is the TEST file of the current 
test, outcome and outcome description obtained my running that TEST. 
With this information this function creates a CONFLICT by copying contests of 
the current TEST file and appends outcome and outcome description it recived *)
               
let create_conflict file outcome1 outcome2 =
  let dir = Filename.dirname file in
  let file_name = dir^"/"^"CONFLICT" in
  let s = read_file file in
  let s2 = s^"\n\n(*above lines are copied from existing TEST file below"
           ^" content is the outcome of running above args with ucdsl."
           ^"\nThis file needs to be deleted for the ucdsl test suite"
    ^"to run this test*)\noutcome:"
           ^outcome1^"\n"^outcome2^".\n" in
  let _ = write_log file_name s2 in
  log_str := !log_str^"\n"^file_name^" created"
      
(* in the above code write_log comes from the file Test_log.ml *)
(* below function parse_file comes into the picture while executing 
a test, we take a TEST file, parse using parse function from 
Test_common_module.ml then get the tokens, match and use the function 
run from Test_common_module.ml
which gives us exit code together with an error message if any
use that information to determine whether a test failed or passed *)
  
let rec parse_file file code =
try
  let parse_list = parse file in
  let str_desc = get_desc parse_list in
  let _ = if str_desc <> "" then
            desc_str := !log_str ^ (get_desc parse_list)
                        ^"-----End of description-----\n"
  in
   let f_name, out_come1, out_come2 = match_expr parse_list [| |] Empty "" 0
   in  let (stat, s_out) =
         run (String.sub file 0 (String.length file -5))
           (Array.append [|"ucdsl"|] f_name) in
    match stat with
    |Some 0 -> begin match out_come1 with
       |Success -> if s_out = "" then
                     (log_str := !log_str
                                 ^ "**Test passed - Outcome is success " 
                                 ^"and exit code is 0"; code)
                   else
                     (log_str := !log_str
                      ^"->Test failed - *ucdsl output is expected to be empty*"
                                 ^"\nOutcome is sucess and exit code is 0"
                     ;create_conflict file "unknown" s_out; code+1)
       |Failure -> (log_str := !log_str
                     ^"->Test failed - *Exit code is 0 but outcome is Failure*"
                               ^s_out; code+1)
       |_ -> (log_str := !log_str ^ "Test failed - Exit code 0 unknown outcome";
              create_conflict file "unknown" s_out; code+1)
               end
    |None -> (let _ = log_str := (!log_str)
                               ^"->Test failed - *ucdsl did not exit normally*"
              in create_conflict file "unknown" s_out;(code+1))
    |Some n -> begin match out_come1 with
       |Failure -> (if s_out = out_come2 then
                      (log_str := !log_str
                       ^"**Test passed - Outcome is failure and exit code is "
                                    ^string_of_int n;
                       code)
                    else
                      (log_str := !log_str
       ^"->Test failed - *ucdsl message is different from* outcome description"
                                    ^"\nOutcome is failure and exit code is "
                                    ^ string_of_int n;
                       create_conflict file "failure" s_out;
                       sec_str := "\n"^"-------"
                                  ^"ucdsl returned:-------\n"
                                  ^s_out
                                  ^"\n-------Outcome message is:-------\n"
                                  ^out_come2;
                       code+1))
       |Success ->  (log_str := !log_str
                  ^"->Test failed - Exit code *0 expected* but exit code is "
                                ^string_of_int n;
                     sec_str := "\nucdsl returned:\n"^s_out;
                     create_conflict file "failure" s_out;code+1)
       |_ -> (log_str := !log_str ^ "->Test failed - *unexpected outcome*;\n" 
                         ^"exit code is "^string_of_int n;
              create_conflict file "unknown" s_out;code+1)
                  end
with
|Test_lexer.Syntax_error e ->let log_err = e in
                  log_str := !log_str ^log_err; (code+1) 
|e -> let log_err = Printexc.to_string e in
      log_str := !log_str ^log_err; (code+1)
                                              
(* log_fun is log function which write the log and prints the log checking 
the verbosity and write_log comes from Test_log.ml*)
                                              
let log_fun () =
  let _ = 
  if !verbose then
    (write_log "log" !desc_str;
     print_endline (!desc_str
                      ^ !log_str ^ !sec_str))
  else if not !quiet then
     print_endline (!log_str ^"\n")
    
  in
     write_log "log" (!log_str ^ !sec_str);
     log_str := "";
     sec_str := "";
     desc_str := ""

(* We take a directory and find all TEST files in the directory,
file_list contains all that information and error_string 
contains any errors happened during searching the directory dir
for TEST files, for example permission denied to read a directory
etc *)     
                                                   
let pre_verbose dir  =
  let file_list, error_string  =  walk_directory_tree dir [] "" in
  (* get TEST files list *)
   let _ = if (error_string <> "") then
             (let _ = write_log "log" error_string in
                     print_endline error_string)
  in
  let s = List.length file_list in
  let _ = if (s = 0) then
            (let _ = log_str := "\nFound 0 files \n" in log_fun(); exit 0)
          else
            let _ = log_str := "\nFound " ^ (string_of_int s) ^
                         " files \n" in log_fun()
  in
  let rec parse_list fil_list exit_code =
    match fil_list with
    |[] -> if (exit_code = 0) then
             (let _ = log_str  := !log_str^
         "Test suite completed sucessfully all tests passed" in
             log_fun(); exit 0)
           else (
             let _ = log_str := !log_str^ "A total of "
                                ^string_of_int exit_code ^
                          " errors found. log file created." in
             log_fun();
             exit 1)
    |e::l -> let _ = log_str := !log_str^e^"\n" in
             let _ = dir_name e in
             let _ = log_str := !log_str in
             let dir_f = Filename.dirname e in
             let file_name = dir_f^"/"^"CONFLICT" in
             if Sys.file_exists(file_name) then
               (let _ =
                 log_str := !log_str^"Test skipped\nError: "^file_name^" exists"
                in
                let _ = sec_str := !sec_str
                                ^"\n\n.._______________________________..\n" in
                let _ = log_fun() in parse_list l (exit_code+1))
             else 
               (let code = parse_file e exit_code in
                sec_str := !sec_str^"\n\n.._______________________________..\n";
                log_fun ();
                parse_list l code)
  in parse_list file_list 0
       
(* For every test all the error messages are stored in string log_str, once
a test ran, depending on verbosity option we choose to display it or not but 
in all times we write it to log *)
                  
  
  
  

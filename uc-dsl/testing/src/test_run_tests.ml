(* test_run_tests.ml *)
open Test_types
open Test_common_module
open Test_log

exception Error of string
                 
let verbose = ref false
let debug = ref false
let quiet = ref false

(* The above 3 variables refer to the options as their name suggests *)


let log_str = ref ""
let sec_str = ref ""
let desc_str = ref ""
             

             
(* check_name contents sees if there any .ec or .uc files in the directory 
if yes then their names will be passed onto check_ec_standard *)
             
let check_name contents  =
  let rec check file_list  =
    match file_list with
    | []     -> ()
    | e :: l ->
       let len = String.length e in
       let _ =
         if len >= 4 &&
              (String.sub e (len - 3) 3 = ".uc" ||
                 String.sub e (len - 3) 3 =  ".ec")
         then log_str := !log_str ^ check_ec_standard e in
       check l in
  check contents
  
(* dir_name takes a file, gets it's directory by using 
Filename.dirname so that the contents can be examined by 
check_name function *)
  
let dir_name file =
  let dir = Filename.dirname file in
  let contents = Array.to_list (Sys.readdir dir) in
  check_name contents

let rec last_element y list = 
  match list with 
  | [] -> raise (Error  "List is empty")
  | [x] -> if y=[| |] then [|x|] else Array.append y [|x|]
  | first_el::rest_of_list -> let z = Array.append y [|first_el|] in
                              last_element z rest_of_list
                              
let rec match_expr expression f_name out_come1 out_come2 =
  match expression with
  |[] -> f_name, out_come1, out_come2
  |e::l -> match e with
           |Args o -> let f_array = last_element [| |] o in
                      match_expr l f_array out_come1 out_come2
           |Outcome (o1, o2) -> match_expr l f_name o1 o2
           |_ -> match_expr l f_name out_come1 out_come2

(* create_conflict has 3 arguments file - 
the TEST file of the current test, 
outcome and 
outcome description obtained my running that TEST. 
With this information this function creates 
a CONFLICT by copying contests of 
the current TEST file and appends outcome and 
outcome description it recived *)
               
let create_conflict file outcome1 outcome2 =
  let dir = Filename.dirname file in
  let file_name = dir ^ "/" ^ "CONFLICT" in
  let s = read_file file in
  let s2 =
    s ^ "\n\n(*The above lines were copied from the existing TEST file."
    ^ " Below, you will find the actual output of ucdsl."
    ^ " Once the conflict is reconciled,"
    ^ " you must delete this file before rerunning dsl-test.*)\noutcome:"
    ^ outcome1 ^ "\n" ^ outcome2 ^ ".\n" in
  let _ = write_log file_name s2 in
  log_str := !log_str ^ "\n" ^ file_name ^ " created\n"
  
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
    let s1,s2 = check_fields parse_list in
    if s1 <> "" then raise (Error s1)
    else
      let _ = log_str := !log_str^s2 in
      let f_name, out_come1, out_come2 = match_expr parse_list [| |] Empty ""
      in  let (stat, s_out) =
            run (String.sub file 0 (String.length file -5))
              (Array.append [|"ucdsl"|] f_name) in
          match stat with
          |Some 0 -> begin match out_come1 with
                     |Success ->
                       if s_out = out_come2 then
                         (log_str := !log_str
                                     ^ "**Test passed - Outcome is success " 
                                     ^"and exit code is 0\n"; code)
                       else
                         (log_str :=
                            !log_str
                            ^ "->Test failed - *ucdsl message is different"
                            ^ "from* outcome description*"
                            ^ "\nOutcome is sucess and exit code is 0\n";
                          create_conflict file "unknown" s_out;
                          code+1)
                     |Failure -> (log_str :=
                                    !log_str
                                    ^ "->Test failed - *Exit code is 0 "
                                    ^ "but outcome is Failure*"
                                    ^ s_out^"\n"; code+1)
                     |_ -> (log_str :=
                              !log_str
                              ^ "Test failed - Exit code 0 unknown outcome\n";
                            create_conflict file "unknown" s_out; code+1)
                     end
          |None -> (let _ = log_str :=
                             !log_str
                             ^"->Test failed - *ucdsl did not exit normally*\n"
                    in create_conflict file "unknown" s_out;(code+1))
          |Some n -> begin match out_come1 with
                     |Failure -> (if s_out = out_come2 then
                                    (log_str :=
                                       !log_str
                                       ^ "**Test passed - Outcome is failure"
                                       ^" and exit code is "
                                       ^string_of_int n^"\n";
                                     code)
                                  else
                                    (log_str :=
                                       !log_str
                                       ^"->Test failed - *ucdsl message is "
                                       ^"different from* outcome description"
                                       ^"\nOutcome is failure and "
                                       ^"exit code is "
                                       ^ string_of_int n;
                                     create_conflict file "failure" s_out;
                                     sec_str :=
                                      "\n"^"-------"
                                      ^"ucdsl returned:-------\n"
                                      ^s_out
                                      ^"\n------Outcome description is"
                                      ^":------\n"
                                       ^out_come2^"\n";
                                     code+1))
                     |Success ->  (log_str :=
                                     !log_str
                                     ^"->Test failed - Exit code *0 "
                                     ^"expected* but exit code is "
                                     ^string_of_int n^"\n";
                                   sec_str := "\nucdsl returned:\n"^s_out^"\n";
                                   create_conflict file "failure" s_out;
                                   code+1)
                     |_ -> (log_str :=
                              !log_str
                              ^"->Test failed - *unexpected outcome*;\n" 
                              ^"exit code is "^string_of_int n^"\n";
                            create_conflict file "unknown" s_out;
                            code+1)
                     end
  with
  |Test_lexer.Syntax_error e -> let log_err = e in
                                log_str := !log_str ^log_err^"\n"; (code+1) 
  |Error e ->                   let log_err = e in
                                log_str := !log_str ^log_err^"\n"; (code+1)
  |e ->                         let log_err = Printexc.to_string e in
                                log_str := !log_str ^log_err^"\n"; (code+1)
                              
(* log_fun is log function which write the log and prints the log checking 
the verbosity and write_log comes from Test_log.ml*)
                                            
let log_fun () =
  let _ = 
    if !verbose then
      (write_log "log" (!desc_str);
       print_string (!desc_str ^ !log_str ^ !sec_str))
    else if not !quiet then
      print_string (!log_str)
    
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
            (let _ = write_log "log" (error_string^"\n") in
             if not !quiet then print_endline error_string)
  in
  let s = List.length file_list in
  let _ = if (s = 0) then
            (let _ = log_str := "\nFound 0 files \n" in log_fun(); exit 0)
          else
            let _ = log_str :=
                      "\nFound "^(string_of_int s) ^" files\n\n" in log_fun()
  in
  let rec parse_list fil_list exit_code =
    match fil_list with
    |[] -> if (exit_code = 0) then
             (let _ = log_str  :=
                        !log_str 
                        ^"Test suite completed sucessfully all tests passed \n"
              in
              log_fun();
              exit 0)
           else (
             let _ =
               log_str :=
                 !log_str^ "A total of " ^string_of_int exit_code
                 ^ " errors found. log file created.\n" in
             log_fun();
             exit 1)
    |e::l -> let _ = log_str := !log_str^e^"\n" in
             let _ = dir_name e in
             let _ = log_str := !log_str in
             let dir_f = Filename.dirname e in
             let file_name = dir_f^"/"^"CONFLICT" in
             if Sys.file_exists(file_name) then
               (let _ =
                  log_str := !log_str^"Test skipped\nError: "
                             ^ file_name
                             ^ " exists\n"
                in
                let _ =
                  sec_str :=
                    !sec_str
                    ^"\n.._______________________________..\n" in
                let _ =
                  log_fun() in
                parse_list l (exit_code+1))
             else 
               (let code = parse_file e exit_code in
                sec_str :=
                  !sec_str
                  ^"\n.._______________________________..\n";
                log_fun ();
                parse_list l code)
  in parse_list file_list 0
       
(* For every test all the error messages are stored in string log_str, once
a test ran, depending on verbosity option we choose to display it or not but 
in all times we write it to log *)
       
       
       
       

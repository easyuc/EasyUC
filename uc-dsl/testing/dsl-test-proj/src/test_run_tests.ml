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
let conflict_str = ref ""
let fail_str = ref ""

let rec last_element y list =
  match list with
  | [] -> raise (Error "List is empty")
  | [ x ] -> if y = [||] then [| x |] else Array.append y [| x |]
  | first_el :: rest_of_list ->
      let z = Array.append y [| first_el |] in
      last_element z rest_of_list

let rec match_expr expression exec args out_come1 out_come2 =
  match expression with
  | [] -> (exec, args, out_come1, out_come2)
  | e :: l -> (
      match e with
      | Exec e -> match_expr l e args out_come1 out_come2
      | Args o ->
          let args_array = last_element [||] o in
          match_expr l exec args_array out_come1 out_come2
      | Outcome (o1, o2) -> match_expr l exec args o1 o2
      | _ -> match_expr l exec args out_come1 out_come2)

(* create_conflict has 3 arguments file - the TEST file of the current
   test, outcome and outcome description obtained my running that
   TEST.  With this information this function creates a CONFLICT by
   copying contests of the current TEST file and appends outcome and
   outcome description it recived *)

let create_conflict file outcome1 outcome2 =
  let dir = Filename.dirname file in
  let file_name = dir ^ "/" ^ "CONFLICT" in
  let s = read_file file in
  let s2 =
    s ^ "\n(*\nThe above lines were copied from the existing TEST file."
    ^ "\nBelow, you will find the actual output of ucdsl."
    ^ "\nOnce the conflict is reconciled,"
    ^ "\nyou must delete this file before rerunning dsl-test.\n*)\noutcome:"
    ^ outcome1 ^ "\n" ^ outcome2 ^ ".\n"
  in
  let _ = write_log file_name s2 in
  log_str := !log_str ^ "\n" ^ file_name ^ " created"

let match_stat stat =
  match stat with Some 0 -> "0" | Some n -> string_of_int n | _ -> "Unknown"

(* in the above code write_log comes from the file Test_log.ml *)

(* below function parse_file comes into the picture while executing a
   test, we take a TEST file, parse using parse function from
   Test_common_module.ml then get the tokens, match and use the
   function run from Test_common_module.ml which gives us exit code
   together with an error message if any use that information to
   determine whether a test failed or passed *)

let parse_file file code =
  try
    let parse_list = parse file in
    let str_desc = get_desc parse_list in
    let _ =
      if str_desc <> "" then
        desc_str :=
          !log_str ^ "\n" ^ get_desc parse_list ^ "-----End of description-----"
    in
    let s1, s2 = check_fields parse_list in
    if s1 <> "" then
      if s2 <> "" then raise (Error (s1 ^ "\n" ^ s2)) else raise (Error s1)
    else
      let _ = log_str := !log_str ^ "\n" ^ s2 in
      let exec, f_name, out_come1, out_come2 =
        match_expr parse_list "" [||] Empty ""
      in
      let out_code, out_text =
        if out_come1 = Success then ("0", "success") else ("1", "failure")
      in
      let stat, s_out =
        if exec = "" then
          run
            (String.sub file 0 (String.length file - 5))
            (Array.append [| "ucdsl" |] f_name)
        else
          run
            (String.sub file 0 (String.length file - 5))
            (Array.append [| exec |] f_name)
      in
      let run_op = match_stat stat in
      match
        if run_op = "0" || run_op = "1" then run_op = out_code
        else if run_op != "Unknown" then out_code = "1"
        else false
      with
      | true -> (
          match s_out = out_come2 with
          | true ->
              log_str :=
                !log_str ^ "** Test passed - outcome is " ^ out_text
                ^ " and exit code is " ^ run_op ^ " **";
              code
          | _ ->
              log_str :=
                !log_str ^ "-> Test failed - UCDSL output differs from "
                ^ "outcome description.\noutcome description is:\n" ^ out_come2
                ^ "UCDSL message is: \n" ^ s_out;
              create_conflict file out_text s_out;
              fail_str := !fail_str ^ file ^ "\n";
              code + 1)
      | _ -> (
          match s_out = out_come2 with
          | false -> (
              match s_out = "" with
              | true ->
                  log_str :=
                    !log_str
                    ^ "-> Test failed - Outcome differs from UCDSL output"
                    ^ "\noutcome is " ^ out_text ^ " but exit code is " ^ run_op
                    ^ "\noutcome description is:\n" ^ out_come2
                    ^ "UCDSL message is empty";
                  create_conflict file
                    (if run_op = "0" then "success" else "failure")
                    s_out;
                  fail_str := !fail_str ^ file ^ "\n";
                  code + 1
              | _ ->
                  log_str :=
                    !log_str
                    ^ "-> Test failed - Outcome differs from UCDSL output"
                    ^ "\noutcome is " ^ out_text ^ " but exit code is " ^ run_op
                    ^ "\noutcome description is:\n" ^ out_come2
                    ^ "UCDSL message is:" ^ s_out;
                  create_conflict file
                    (if run_op = "0" then "success" else "failure")
                    s_out;
                  fail_str := !fail_str ^ file ^ "\n";
                  code + 1)
          | _ ->
              log_str :=
                !log_str ^ "-> Test failed - Exit code differs from outcome\n"
                ^ "outcome is " ^ out_text ^ " but exit code is " ^ run_op;
              create_conflict file
                (if run_op = "0" then "success" else "failure")
                s_out;
              fail_str := !fail_str ^ file ^ "\n";
              code + 1)
  with
  | Test_lexer.Syntax_error e ->
      log_str := !log_str ^ "\n" ^ e;
      fail_str := !fail_str ^ file ^ "\n";
      code + 1
  | Error e ->
      let log_err = e in
      log_str := !log_str ^ "\n" ^ log_err;
      fail_str := !fail_str ^ file ^ "\n";
      code + 1
  | e ->
      let log_err = Printexc.to_string e in
      log_str := !log_str ^ "\n" ^ log_err;
      fail_str := !fail_str ^ file ^ "\n";
      code + 1

(* log_fun is log function which write the log and prints the log
   checking the verbosity and write_log comes from Test_log.ml*)

let log_fun () =
  let _ =
    if !verbose then (
      write_log "log" !desc_str;
      print_endline (!desc_str ^ !log_str ^ !sec_str))
    else if not !quiet then print_endline !log_str
  in

  write_log "log" (!log_str ^ !sec_str ^ "\n");
  log_str := "";
  sec_str := "";
  desc_str := ""

let log_fail () =
  match !fail_str = "" with
  | false -> (
      match !conflict_str = "" with
      | false ->
          log_str :=
            "Failed tests:\n" ^ !fail_str ^ "\nSkipped tests\n" ^ !conflict_str
      | true -> log_str := !fail_str)
  | true -> log_str := "Skipped tests\n" ^ !conflict_str

(* We take a directory and find all TEST files in the directory,
   file_list contains all that information and error_string contains
   any errors happened during searching the directory dir for TEST
   files, for example permission denied to read a directory etc *)

let pre_run dir =
  let file_list, error_string = walk_directory_tree dir [] "" in
  (* get TEST files list *)
  let _ =
    if error_string <> "" then
      let _ = write_log "log" (error_string ^ "\n") in
      if not !quiet then print_endline error_string
  in
  let s = List.length file_list in
  let _ =
    if s = 0 then (
      let _ = log_str := "\nFound 0 files" in
      log_fun ();
      exit 0)
    else
      let _ = log_str := "\nFound " ^ string_of_int s ^ " files" in
      let _ = desc_str := "" in
      log_fun ()
  in
  let rec parse_list fil_list exit_code =
    match fil_list with
    | [] ->
        if exit_code = 0 then (
          let _ =
            log_str :=
              !log_str
              ^ "\nTest suite completed sucessfully all tests passed \n"
          in
          log_fun ();
          exit 0)
        else
          let _ =
            log_str :=
              !log_str ^ "\nTest suite found issues with the followng tests\n"
          in
          log_fun ();
          log_fail ();
          log_str :=
            !log_str ^ "\n" ^ string_of_int exit_code ^ " errors found.\n";
          log_fun ();
          exit 1
    | e :: l ->
        let _ = log_str := !log_str ^ "\n" ^ e in
        let file_name = Filename.dirname e ^ "/" ^ "CONFLICT" in
        if Sys.file_exists file_name then (
          let _ =
            log_str :=
              !log_str ^ "\nError: " ^ file_name ^ " exists. \nTest skipped.";
            conflict_str := !conflict_str ^ file_name ^ "\n"
          in
          let _ =
            sec_str := !sec_str ^ "\n.._______________________________.."
          in
          log_fun ();
          parse_list l (exit_code + 1))
        else
          let code = parse_file e exit_code in
          sec_str := !sec_str ^ "\n.._______________________________..";
          log_fun ();
          parse_list l code
  in
  parse_list file_list 0

(* For every test all the error messages are stored in string log_str,
   once a test ran, depending on verbosity option we choose to display
   it or not but in all times we write it to log *)

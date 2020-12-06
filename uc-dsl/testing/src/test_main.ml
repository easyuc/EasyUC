(* test_main.ml *)
open Test_run_tests
open Test_log
open Test_common_module
   
      
let dirs_list = ref []

(* Checks whether the input a valid directory or not *)
             
let insert_dirs x =
  (* print_endline x;*)
  dirs_list := !dirs_list @ [x] 
  
let verify_dir dir =
  try
    let _ =
      Sys.is_directory(dir) in dir
  with
  |Sys_error e ->
    try
      let _ =
        Sys.is_directory("./"^dir) in
      ("./"^dir)
    with
    |Sys_error e ->
      (print_endline e; exit 1)
     
(* needs to be logged? *)
(* this function pre_debug comes into the picture when debug option is used
we take a file, parse it using parse function from Test_common_module.ml and 
print it using print_list function from the same file *)
                              
let pre_debug file =
  try
    let list = parse file in
    let _ = print_list list in
    let (s1, s2) = check_fields list in
    print_string (s1^s2);
    print_endline "___END___";
    exit 0
  with
  |Sys_error e ->
    (if (e="Is a directory") then
       (print_endline (file^" "^e);
        print_endline "debug expects a 'TEST' file";
        exit 1)
     else
       (print_endline e;exit 1))
  |Test_lexer.Syntax_error e ->
    print_endline e;
    exit 1
  |Error e ->
    print_endline e;
    exit 1
  |e ->
    print_endline (Printexc.to_string e);
    exit 1

(* call_dir_test is the sanity check for options
and creates log file if it doesn't exist 
create_log function is at Test_log.ml  *)
           
let call_dir_test () =
  let _ =
    if not (!verbose || !quiet || !debug)
    then
      dirs_list :=  ["none"] @ !dirs_list;
  in
  let () =
    if (List.length !dirs_list < 2) then
      (print_string "Argument is expected; none provided\n";
       exit 1)
    else if(List.length !dirs_list > 2) then
      (print_string "Too many arguments given\n";
       exit 1)
  in
  if !debug then
    (let x =
       List.nth !dirs_list 1 in
     if Sys.file_exists x then
       pre_debug x
     else if (Sys.file_exists ("./"^x)) then
       pre_debug ("./"^x)
     else  (print_endline (x^" not found"); exit 1))
  else
    (let b =
       verify_dir (List.nth !dirs_list 1) in
     let _ =
       create_log () in
     pre_run b)

let usage_msg =
  "Usage: dsl-test [verbosity option] dir\n       dsl-test -debug file"

let check_verbosity str  =
  if not (!verbose || !quiet || !debug) &&
       List.length !dirs_list = 0 then
    (insert_dirs str;
     0)
  else if (!verbose || !quiet || !debug) then
    (print_endline "Only one option is allowed";
     1)
  else
    (print_endline ((List.nth !dirs_list 0)
                    ^ " is not allowed before -"
                    ^ str);
     1)

let main =
  begin
    let rec speclist =
      [("-verbose",
        Arg.Unit
          (fun () ->
            if check_verbosity "verbose" = 0 then
              verbose := true
            else (
              Arg.usage speclist usage_msg;
              exit 1)),
        "Verbosity option: enables verbose mode");
       ("-quiet",
        Arg.Unit
          (fun () ->
            if  check_verbosity "quiet" = 0 then
              quiet := true
            else (
              Arg.usage speclist usage_msg;
              exit 1)),
        "Verbosity option: enables quiet mode");
       ("-debug",
        Arg.String
          (fun x ->
            if check_verbosity "debug" = 0 then
              (debug := true;
               insert_dirs x)
            else (
              Arg.usage speclist usage_msg;
              exit 1)),
        "Prints debug information of a TEST file");
      ]
    in
    Arg.parse speclist
      (fun x ->
(*        if not (!verbose || !quiet || !debug) && then
          (print_endline ("Unknown option "^ x);
           Arg.usage speclist usage_msg;
           exit 1)
        else *)
        insert_dirs x)
      usage_msg;
    call_dir_test;
  end

let () = main ()

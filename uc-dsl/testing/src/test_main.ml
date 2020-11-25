(* test_main.ml *)
open Test_run_tests
open Test_log
open Test_common_module
   
      
let dirs_list = ref []

(* Checks whether the input a valid directory or not *)
             
              
let check_dirs anon =
(*  let _ = print_endline anon in *)
  if (List.length !dirs_list <> 0) then 1
  else
     (dirs_list := (!dirs_list) @ [anon]; 0)

let verify_dir dir =
  try
    let _ = Sys.is_directory(dir) in dir
  with
  |Sys_error e -> try
                  let _ = Sys.is_directory("./"^dir) in ("./"^dir)
                with
                |Sys_error e -> (print_endline e; exit 1)
                             
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
    |Sys_error e -> (if (e="Is a directory") then
                       (print_endline (file^" "^e);
                        print_endline "debug expects a 'TEST' file";
                        exit 1)
                     else
                       (print_endline e;exit 1))
    |e -> print_endline (Printexc.to_string e); exit 1

(* call_dir_test is the sanity check for options
and creates log file if it doesn't exist 
create_log function is at Test_log.ml  *)
           
let call_dir_test dir_list_local =
    let _ = if (List.length dir_list_local <> 1) then
    (print_string "Directory is expected; none provided\n"; exit 1)
    in
    let _ = if !debug then ( pre_debug (List.nth dir_list_local 0))
    in 
    let b = verify_dir (List.nth dir_list_local 0) in
    let _ = create_log () in
    pre_run b
let usage_msg = "Usage: dsl-test [verbosity option] dir\ndsl-test -debug file"

let main =
begin
  let rec speclist = [("-verbose", Arg.Rest (fun x -> let r =  check_dirs x in
                                                 if r = 0 then verbose := true
                                                 else (
                                  print_endline "Only one option is allowed";
                                  Arg.usage speclist usage_msg;
                                                       exit 1)
                                 ), "Verbosity option: enables verbose mode");
                ("-quiet", Arg.Rest (fun x -> let r = check_dirs x in
                                              if r = 0 then quiet := true
                                              else (
                                   print_endline "Only one option is allowed";
                                   Arg.usage speclist usage_msg;
                                                    exit 1)
                             ), "Verbosity option: enables quiet mode");
                ("-debug", Arg.Rest
                             (fun x -> let _ = check_dirs x in
                              if Sys.file_exists x then pre_debug x
                              else if (Sys.file_exists ("./"^x)) then
                                pre_debug ("./"^x)
                              else  print_endline (x^" not found"); exit 1)
                 , "Prints debug information of a TEST file")
               ]
in
Arg.parse speclist (fun anon -> let r = check_dirs anon in
                                if r <> 0 then
                                  (print_endline "Only one option is allowed";
                                   Arg.usage speclist usage_msg;
                                   exit 1)) usage_msg;
   call_dir_test !dirs_list
end

let () = main

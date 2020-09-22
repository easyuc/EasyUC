(* main.ml *)
open Test_create  
open Pre
open Test_log
open Test_main
   
   
   
let dirs_list = ref []

              
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
                |Sys_error e -> (print_endline e;
                                 print_endline (dir^" is not a valid directory \n"); exit 1)
(* needs to be logged? *)

let pre_debug file =
    try
      print_list (parse file); exit 0
    with
      e -> print_endline (Printexc.to_string e); exit 1

let call_dir_test dir_list_local =
    let _ = if (List.length dir_list_local <> 1) then
    (print_string "No directory given \n"; exit 1)
    in
    let _ = if !debug then ( pre_debug (List.nth dir_list_local 0))
    in 
    let b = verify_dir (List.nth dir_list_local 0) in
    let _ = create_log () in
    pre_verbose b
let usage_msg = "Usage: dsl-test [verbosity option] dir\ndsl-test -debug file"

let main =
begin
  let rec speclist = [("-verbose", Arg.Rest (fun x -> let r =  check_dirs x in
                                                 if r = 0 then verbose := true
                                                 else (print_endline "Only one option is allowed";
                                                       Arg.usage speclist usage_msg;
                                                       exit 1)
                                 ), "Verbosity option: enables verbose mode");
                ("-quiet", Arg.Rest (fun x -> let r = check_dirs x in
                                              if r = 0 then quiet := true
                                              else (print_endline "Only one option is allowed";
                                                    Arg.usage speclist usage_msg;
                                                    exit 1)
                             ), "Verbosity option: enables quiet mode");
                ("-debug", Arg.Rest
                             (fun x -> let _ = check_dirs x in
                              if Sys.file_exists x then pre_debug x
                              else if (Sys.file_exists ("./"^x)) then pre_debug ("./"^x)
                              else  print_endline (x^" not found"); exit 1)
                 , "Prints debug information of a TEST file");
("-create", Arg.Rest
                             (fun x -> let _ = check_dirs x in
                              if Sys.file_exists x then pre_create x
                              else if (Sys.file_exists ("./"^x)) then pre_create ("./"^x)
                              else  print_endline (x^" not found"); exit 1), "Create TEST files mode");
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

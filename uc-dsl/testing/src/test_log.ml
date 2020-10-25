(* test_log.ml *)

(* get1char reads a character without pressing enter.
 Source: Jeffrey Scofield, however this doesn't work in Windows; 
since tcgetattr is not implemented yet in windows *)

let get1char () =
    let termio = Unix.tcgetattr Unix.stdin in
    let _ = Unix.tcsetattr Unix.stdin Unix.TCSADRAIN
            { termio with Unix.c_icanon = false } in
    let res = input_char stdin in
    Unix.tcsetattr Unix.stdin Unix.TCSADRAIN termio;
    res

let create_log () =
  try
    let file_name = "log" in
    let folder = Sys.getcwd() in
    let _ = if Sys.file_exists(folder^"/"^file_name) then
            (let _ =  print_endline
          "log already exists, press O/o to overwrite any other key to exit" in
              let char = get1char() in
              if (char <> 'o' && char <> 'O') then exit 1 )
    in
    let oc = open_out (folder^"/"^file_name) in
    close_out oc            
  with e ->  print_endline (Printexc.to_string e); exit 1

let write_log file str =
  try
    let out =
      open_out_gen [Open_wronly; Open_append; Open_creat; Open_text] 0o666
      (Sys.getcwd()^"/"^file) in
       output_string out str;
       close_out out
  with e ->  print_endline (Printexc.to_string e); exit 1
             

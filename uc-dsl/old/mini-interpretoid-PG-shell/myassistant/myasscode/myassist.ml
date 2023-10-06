let print_error (e : string) : unit =
  print_endline ("Error:"^e)

let str_dot (s : string) : string =
  let n = String.length s in
  if n > 0 && s.[n-1] = '.' then
    begin
      let ret = String.sub s 0 (n-1) in
      if ret = "quit" then exit 0 else ret
    end
  else
    raise (Failure "does not end with .")
    
let state_c = ref 0
let filenam = ref ""

let print_state () : unit =
  let begpos, endpos = 
  ((string_of_int !state_c), (string_of_int (2 * !state_c))) in
  print_endline ("UC file position: "^(!filenam)^" "^begpos^" "^endpos^";");
  print_endline ("state:"^(string_of_int !state_c)^";");
  state_c := !state_c+1

let rec get_file_name () : string =
  print_string ">";
  let s = read_line () in

  try
    Scanf.sscanf s "load %s%!" (fun f -> str_dot f)
  with _ -> print_error "load file first!";
  get_file_name ()
  
let rec loop () : unit =
  print_string ">";
  let s = read_line () in
  let c = 
    try
     Scanf.sscanf s "%s%!" (fun f -> str_dot f)
    with _ -> print_error "Command must end with ."; ""
  in
  if c="done"
  then ()
  else begin print_state(); loop () end

let rec fileloop () : unit =
  filenam := get_file_name ();
  print_state ();
  loop ();
  fileloop ()
  
let () = fileloop ()



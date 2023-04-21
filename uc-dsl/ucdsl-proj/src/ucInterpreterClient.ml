let stdIOclient 
(parsecom: in_channel -> 'a)
(is_quitcom : 'a -> bool) 
(execcom : 'a -> string) : unit =
  let command = ref (parsecom stdin) in
  while (is_quitcom !command) = false do
    let ret_str = execcom !command in
    print_endline ret_str;
    command := parsecom stdin
  done
  
let dummy_parsecom (ch : in_channel) : string =
  input_line ch
  
let dummy_is_quitcom (comm : string) : bool =
  comm = "quit"
  
let dummy_execcom (comm : string) : string =
  "Received "^comm^" command."
  
let main =
  stdIOclient dummy_parsecom dummy_is_quitcom dummy_execcom
  
 

open UcSpec
open UcLexer
open UcMessage
open EcLocation
open UcInterpreter
open UcTypedSpec
open UcSpecTypedSpecCommon
module L = Lexing

let reset_pos_rename (lexbuf : L.lexbuf) (name : string) : unit =
   let init_pos = {
        L.pos_fname = name;
        L.pos_lnum  = 1;
        L.pos_bol   = 0;
        L.pos_cnum  = 0
      }
   in
   lexbuf.L.lex_curr_p <- init_pos

let lexbuf_from_channel (name : string) (ch : in_channel) =
  let lexbuf = L.from_channel ~with_positions:true ch in
  reset_pos_rename lexbuf name;
  lexbuf

let next_cmd (lexbuf : L.lexbuf) : interpreter_command =
  try UcParser.interpreter_command read lexbuf
  with
  | UcParser.Error ->
      (error_message  (* no need to close channel *)
       (EcLocation.make lexbuf.L.lex_start_p lexbuf.L.lex_curr_p)
       (fun ppf -> Format.fprintf ppf "@[parse@ error@]"))

type interpreter_state = 
  {
    setup_complete : bool;
    cmd_no : int;
    root : string option;
    maps : maps_tyd option;
    worlds : worlds option; 
    w : world option(*replace with contexts etc.*)
  }

let init_state : interpreter_state =
  {
    setup_complete = false;
    cmd_no = 0;
    root = None;
    maps = None;
    worlds =  None; 
    w = None;
  }



let stack : interpreter_state list ref = ref []
let currs() : interpreter_state =
  List.hd !stack

let push (is : interpreter_state) : unit =
  stack := is :: !stack 

let cmd_prompt (cmd_no : int) =
  let cmd_no_str = string_of_int cmd_no in
  "#"^cmd_no_str^">"

let print_prompt () : unit =
  print_endline (cmd_prompt (currs()).cmd_no)

let cmd_name () =
  "cmd #"^(string_of_int (currs()).cmd_no)

let interpret (lexbuf : L.lexbuf) =

  let print_state () : unit =
    let c = currs() in
    let begpos, endpos = 
    ((string_of_int c.cmd_no), (string_of_int (2 * c.cmd_no))) in
    begin match c.root with
    | Some f ->
      let filenam = f^".uc" in
      print_endline ("UC file position: "^(filenam)^" "^begpos^" "^endpos^";")
    | None -> ()
    end
    ;
    print_endline ("state:"^(string_of_int c.cmd_no)^";")
  in

  let prompt () : unit =
    print_state();
    print_prompt()
  in

  let load (psym : psymbol) : unit =
    let file = unloc psym in
    let root =
    try   
      UcUtils.capitalized_root_of_filename_with_extension file 
    with _ ->
      error_message (loc psym)
      (fun ppf -> Format.fprintf ppf 
      "@[invalid@ filename@ %s,@ filename @ should@ have@ .uc@ suffix.@]" file)
    in
    let maps = UcParseAndTypecheckFile.parse_and_typecheck_file_or_id
    (UcParseFile.FOID_File file) in
    let c = currs() in
    let news = 
      { c with
        cmd_no = c.cmd_no+1;
        root = Some root;
        maps = Some maps;
        worlds = None;
        w = None;
      } in
    push news
  in

  let worlds (fe : fun_expr): unit =
    let c = currs() in
    let worlds = 
      fun_expr_to_worlds (Option.get c.root) (Option.get c.maps) fe 
    in
    pp_worlds Format.std_formatter worlds;
    let news = 
      {
        c with
        cmd_no = c.cmd_no+1;
        worlds = Some worlds;
        w = None;
      } in
    push news
  in

  let world (w : world) : unit =
    let c = currs() in
    let news = 
    {
      c with
      cmd_no = c.cmd_no+1;
      w = Some w;
      setup_complete = true;
    } in
    push news
  in

  let inc_cmd_no () : unit =
    let c = currs() in
    let news = { c with cmd_no = c.cmd_no+1 } in
    push news
  in

  let undo (pi : int located) : unit =
    let i = unloc pi in
    let l = List.length !stack in
    if ((i < l) && (i > 0)) 
    then
      stack := BatList.drop i (!stack)
    else
      error_message (loc pi)
        (fun ppf -> Format.fprintf ppf 
"@[%i@ is@ not@ between@ 0@ and@ %i@]" i l)
  in
  
  let donec () : unit =
    let c = currs() in
    let news =  
      {
        c with
        cmd_no = c.cmd_no+1;
        setup_complete = false
      } in
    push news
  in

  let rec done_loop (): unit =
    try
      let cmd = next_cmd lexbuf in
      begin  match (unloc cmd) with
      | Send _  -> inc_cmd_no()
      | Run -> inc_cmd_no()
      | Step -> inc_cmd_no()
      | Addv _ -> inc_cmd_no() (*TODO add to parser*)
      | Addf _ -> inc_cmd_no() (*TODO add to parser*)
      | Prover _ -> inc_cmd_no()
      | Back pi -> undo pi
      | Finish -> donec ();()
      | Quit -> exit 0
      | _ ->
        error_message (loc cmd)
        (fun ppf -> Format.fprintf ppf 
"@[one@ of@ following@ commands@ expected:@ send@,run@,step@,addv@,addf@,prover@@,back@,finish.@]")
      end
    with _ ->
      prompt();
      done_loop()
  in
 
  let rec restart_loop () : unit =
    try
      let cmd = next_cmd lexbuf in
      begin match (unloc cmd) with
      | Load psym ->
        load psym
        
      | Funex fe ->
        worlds fe

      | World w -> 
        world w
        
      | Quit -> exit 0
      | _ ->
        error_message (loc cmd)
        (fun ppf -> Format.fprintf ppf 
"@[one@ of@ following@ commands@ expected:@ load@,functionality@,real@,ideal@,quit.@]")
      end
    with _ ->
      prompt();
      restart_loop()
  in

let rec load_loop () : unit =
    try 
      let cmd = next_cmd lexbuf in
      begin  match (unloc cmd) with
      | Load psym ->
        load psym
      | Quit -> exit 0
      | _ ->
        error_message (loc cmd)
        (fun ppf -> Format.fprintf ppf "@[load@ command@ expected@]")
      end
    with _ ->
      prompt();
      load_loop ()
  in

  let rec funexp_loop () : unit = 
    try 
      let cmd = next_cmd lexbuf in
      begin  match (unloc cmd) with
      | Funex fe ->
        worlds fe
      | Quit -> exit 0
      | _ ->
        error_message (loc cmd)
        (fun ppf -> Format.fprintf ppf "@[functionality@ command@ expected@]")
      end
    with _ ->
      prompt();
      funexp_loop() 
  in

  let rec world_loop () : unit=
    try
      let cmd = next_cmd lexbuf in 
      begin  match (unloc cmd) with
      | World w ->
        world w
      | Quit -> exit 0
      | _ ->
        error_message (loc cmd)
        (fun ppf -> Format.fprintf ppf "@[world@ command@ expected@]")
      end
    with _ ->
      prompt();
      world_loop()
  in

  let complete_loop () : unit =
    let c = currs() in
    match c.root with
    | None -> load_loop()
    | Some _ ->
      match c.worlds with
      | None -> funexp_loop()
      | Some _ -> world_loop()
  in

  let setup_loop () : unit =
    match (currs()).w with
    | Some w ->
      restart_loop()
    | None ->
      complete_loop ()
  in

  let rec interpreter_loop (): unit =
    prompt();
    if (currs()).setup_complete
    then
      done_loop()
    else
      setup_loop()
    ;
    interpreter_loop()
  in
  
  stack := [];
  stack := init_state::!stack;
  interpreter_loop()
  
let stdIOclient =
  UcEcInterface.init ();
  let lexbuf = lexbuf_from_channel "stdin" stdin  in
  interpret lexbuf
  
 

open UcSpec
open UcLexer
open UcMessage
open EcLocation
open UcInterpreter
open UcTypedSpec
open UcSpecTypedSpecCommon
module L = Lexing

let reset_pos_rename (lexbuf : L.lexbuf) (name : string) : L.lexbuf =
   lexbuf.L.lex_curr_p <- {
        L.pos_fname = name;
        L.pos_lnum  = 1;
        L.pos_bol   = 0;
        L.pos_cnum  = 0
      };
    lexbuf

let lexbuf_from_channel (name : string) (ch : in_channel) =
  let lexbuf = L.from_channel ch in
  reset_pos_rename lexbuf name

let next_cmd (lexbuf : L.lexbuf) : interpreter_command =
  try UcParser.interpreter_command read lexbuf
  with
  | UcParser.Error ->
      (error_message  (* no need to close channel *)
       (EcLocation.make lexbuf.L.lex_start_p lexbuf.L.lex_curr_p)
       (fun ppf -> Format.fprintf ppf "@[parse@ error@]"))

let cmd_prompt (cmd_no : int) =
  let cmd_no_str = string_of_int cmd_no in
  "#"^cmd_no_str^">"

let cmd_no = ref 0

type interpreter_state = 
  {
    root : string;
    maps : maps_tyd;
    worlds : worlds; 
    w : world (*replace with contexts etc.*)
  }

let interpret (lexbuf : L.lexbuf) (repos : L.lexbuf -> string -> L.lexbuf) =

  let do_load (psym : psymbol) : string * maps_tyd =
    let file = unloc psym in
    let root = 
    UcUtils.capitalized_root_of_filename_with_extension file in 
    let maps = UcParseAndTypecheckFile.parse_and_typecheck_file_or_id
    (UcParseFile.FOID_File file) in
    root, maps
  in

  let rec load_loop () : string * maps_tyd =
    let cmd = next_cmd lexbuf in
    try 
      begin  match (unloc cmd) with
      | Load psym ->
        do_load psym
      | _ ->
        error_message (loc cmd)
        (fun ppf -> Format.fprintf ppf "@[load@ command@ expected@]")
      end
    with _ ->
      load_loop ()
  in

  let do_worlds (root : string) (maps : maps_tyd) (fe : fun_expr): worlds =
    let worlds = fun_expr_to_worlds root maps fe in
    pp_worlds Format.std_formatter worlds;
    worlds
  in

  let rec funexp_loop (root : string) (maps : maps_tyd) : worlds = 
    let cmd = next_cmd lexbuf in
    try 
      begin  match (unloc cmd) with
      | Funex fe -> do_worlds root maps fe
      | _ ->
        error_message (loc cmd)
        (fun ppf -> Format.fprintf ppf "@[functionality@ command@ expected@]")
      end
    with _ ->
      funexp_loop root maps 
  in

  let do_world (root : string) (maps : maps_tyd) (worlds : worlds) (w : world)
  : interpreter_state =
    {
      root = root;
      maps = maps;
      worlds = worlds;
      w = w
    }
  in

  let rec 
  world_loop 
  (root : string) (maps : maps_tyd) (worlds : worlds) : interpreter_state =
    let cmd = next_cmd lexbuf in
    try 
      begin  match (unloc cmd) with
      | World w -> do_world root maps worlds w
      | _ ->
        error_message (loc cmd)
        (fun ppf -> Format.fprintf ppf "@[world@ command@ expected@]")
      end
    with _ ->
      world_loop root maps worlds
  in

  let rec done_loop (): unit =
    let cmd = next_cmd lexbuf in
    try 
      begin  match (unloc cmd) with
      | Send _  -> ()
      | Run -> ()
      | Step -> ()
      | Addv _ -> () (*TODO add to parser*)
      | Addf _ -> () (*TODO add to parser*)
      | Prover _ -> ()
      | Done -> ()
      | _ ->
        error_message (loc cmd)
        (fun ppf -> Format.fprintf ppf 
"@[one@ of@ following@ commands@ expected:@ send@,run@,step@,addv@,addf@,prover@,done.@]")
      end
    with _ ->
      done_loop ()
  in

  let start : interpreter_state =
    let root, maps = load_loop () in
    let worlds = funexp_loop root maps in
    world_loop root maps worlds
  in
 
  let rec restart_loop (ints : interpreter_state) : interpreter_state =
    let root = ints.root in
    let maps = ints.maps in
    let worlds = ints.worlds 
    in
    let cmd = next_cmd lexbuf in
    try 
      begin match (unloc cmd) with
      | Load psym ->
        let root, maps = do_load psym in
        let worlds = funexp_loop root maps in
        world_loop root maps worlds
      | Funex fe ->
        let worlds = do_worlds root maps fe in
        world_loop root maps worlds
      | World w -> 
        do_world root maps worlds w
      | Quit -> exit 0
      | _ ->
        error_message (loc cmd)
        (fun ppf -> Format.fprintf ppf 
"@[one@ of@ following@ commands@ expected:@ load@,functionality@,real@,ideal@,quit.@]")
      end
    with _ ->
      restart_loop ints
  in

  let rec interpreter_loop (ints : interpreter_state) : unit =
    done_loop ();
    let ints = restart_loop ints in
    interpreter_loop ints
  in

  let ints = start in
  interpreter_loop ints
  
let stdIOclient =
  let lexbuf = lexbuf_from_channel (cmd_prompt !cmd_no) stdin  in
  interpret lexbuf reset_pos_rename
  
 

(*
TODO: update this to work with the configuration type and
functions in ucInterpreter.ml, ucInterpreter.mli
*)

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
    cmd_no : int;
    ucdsl_new : bool;
    post_done : bool;
    root : string option;
    maps : maps_tyd option;
    config_gen : config option;
    config : config option;
    effect : effect option
  }

let init_state : interpreter_state =
  {
    cmd_no = 0;
    ucdsl_new = false;
    post_done = false;
    root = None;
    maps = None;
    config_gen = None;
    config = None;
    effect = None;
  }



let stack : interpreter_state list ref = ref []
let currs() : interpreter_state =
  List.hd !stack

let push (is : interpreter_state) : unit =
  stack := is :: !stack

let pop() : unit =
  stack := List.tl !stack

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
    let loco = 
      match c.config with
      | Some config ->
        if ((is_real_running_config config) || (is_ideal_running_config config))
        then loc_of_running_config_next_instr config
        else None
      | None -> None
    in
    begin match loco with
    | Some l ->
      let b,s = (string_of_int l.loc_bchar),(string_of_int l.loc_echar) in
      print_endline ("UC file position: "^(l.loc_fname)^" "^b^" "^s^";")
    | None -> ()
    end
    ;
    match c.config with
    | Some config -> pp_config Format.std_formatter config
    | None ->
      match c.config_gen with
      | Some config -> pp_config Format.std_formatter config
      | None -> 
        match c.maps with
        | Some _ -> 
          print_endline ("state: uc file "^(Option.get c.root)^" loaded;")
        | None   ->
          print_endline ("state: uc file not loaded;")
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
    EcCommands.ucdsl_new();
    let maps =
    try
      Some
      ( UcParseAndTypecheckFile.parse_and_typecheck_file_or_id
        (UcParseFile.FOID_File file)) 
    with _ -> 
        EcCommands.ucdsl_end();
        None
    in
    let c = currs() in
    let news = 
      { c with
        cmd_no = c.cmd_no+1;
        ucdsl_new = true;
        post_done = false;
        root = Some root;
        maps = maps;
        config_gen = None;
        config = None;
        effect = None;
      } in
    push news
  in

  let funexp (fe : fun_expr): unit =
    let c = currs() in
    let config_gen = create_gen_config 
      (Option.get c.root)
      (Option.get c.maps)
      (UcEcInterface.env ())
      fe
    in
    let news = 
      {
        c with
        cmd_no = c.cmd_no+1;
        ucdsl_new = false;
        post_done = false;
        config_gen = Some config_gen;
        config = None;
        effect = None;
      } in
    push news
  in

  let world (w : world) : unit =
    let c = currs() in
    let config_gen = Option.get c.config_gen in
    let config =
      match w with
      | Real -> real_of_gen_config config_gen
      | Ideal -> ideal_of_gen_config config_gen
    in
    let news = 
    {
      c with
      cmd_no = c.cmd_no+1;
      ucdsl_new = false;
      post_done = false;
      config = Some config;
      effect = None;
    } in
    push news
  in

  let inc_cmd_no () : unit =
    let c = currs() in
    let news = 
    { c with 
      cmd_no = c.cmd_no+1;
      ucdsl_new = false;
      post_done = false; 
    } in
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
        ucdsl_new = false;
        post_done = true;
        config = None;
        effect = None;
      } in
    (* we pop all interpreter states until the one that preceeds 
       the start of the experiment *)
    while ((currs()).config!=None) do pop() done;
    push news
  in

  let send (sme : sent_msg_expr) : unit =
    let c = currs() in
    let cconfig = Option.get c.config in
    let conf, eff = send_message_to_real_or_ideal_config cconfig sme in
    let news =  
      {
        c with
        cmd_no = c.cmd_no+1;
        ucdsl_new = false;
        post_done = false;
        config = Some conf;
        effect = Some eff;
      } in
    push news
  in

  let step () : unit =
    let c = currs() in
    let cconfig = Option.get c.config in
    let conf, eff = step_running_or_sending_real_or_ideal_config cconfig in
    let news =  
      {
        c with
        cmd_no = c.cmd_no+1;
        ucdsl_new = false;
        post_done = false;
        config = Some conf;
        effect = Some eff;
      } in
    push news
  in

  let run () : unit =

    let rec runr (conf : config) : config * effect =
      let conf, eff = step_running_or_sending_real_or_ideal_config conf in
      if (eff != EffectOK)
      then conf,eff
      else runr conf
    in
    
    let c = currs() in
    let cconfig = Option.get c.config in
    let conf, eff = runr cconfig in
    let news =  
      {
        c with
        cmd_no = c.cmd_no+1;
        ucdsl_new = false;
        post_done = false;
        config = Some conf;
        effect = Some eff;
      } in
    push news
  in
  

  let modify_config (modify : config -> config) : unit =
    let c = currs() in
    match c.config with
    | Some cf ->
      begin try
        let conf = modify cf in
        let news =  
        {
          c with
          cmd_no = c.cmd_no+1;
          ucdsl_new = false;
          post_done = false;
          config = Some conf;
          effect = None;
        } in
        push news
      with _ -> () end
    | None ->
      let cf = Option.get c.config_gen in
      try
        let conf = modify cf in
        let news =  
        {
          c with
          cmd_no = c.cmd_no+1;
          ucdsl_new = false;
          post_done = false;
          config_gen = Some conf;
          effect = None;
        } in
        push news
      with _ -> ()
  in

  let addv (tb : type_binding) : unit =
    let mdfy cf = add_var_to_config cf tb.id tb.ty in
    modify_config mdfy
  in

  let addf (psy : psymbol) (pex : pexpr) : unit =
    let mdfy cf = add_hyp_to_config cf psy pex in
    modify_config mdfy
  in

  let prover (ppinfo : EcParsetree.pprover_infos) : unit =
    let mdfy cf = update_prover_infos_config cf ppinfo in
    modify_config mdfy
  in

  let rec done_loop (): unit =
    try
      let cmd = next_cmd lexbuf in
      begin  match (unloc cmd) with
      | Send sme  -> send sme
      | Run -> run()
      | Step -> step()
      | Addv tb -> addv tb (*TODO add to parser*)
      | Addf (psy,pex) -> addf psy pex (*TODO add to parser*)
      | Prover ppinfo -> prover ppinfo
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
        funexp fe
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
      | Addv _ -> inc_cmd_no() (*TODO add to parser*)
      | Addf _ -> inc_cmd_no() (*TODO add to parser*)
      | Prover _ -> inc_cmd_no()  

      | World w ->
        world w
      | Quit -> exit 0
      | _ ->
        error_message (loc cmd)
        (fun ppf -> Format.fprintf ppf "@[addv@,addf@,prover@,@ or@ world@ command@ expected@]")
      end
    with _ ->
      prompt();
      world_loop()
  in

  let complete_loop () : unit =
    let c = currs() in
    match c.maps with
    | None -> load_loop()
    | Some _ ->
      match c.config_gen with
      | None -> funexp_loop()
      | Some _ -> world_loop()
  in
 
  let rec restart_loop () : unit =
    try
      let cmd = next_cmd lexbuf in
      begin match (unloc cmd) with
      | Load psym ->
        load psym
        
      | Funex fe ->
        funexp fe

      | World w -> 
        world w
      | Addv _ -> inc_cmd_no() (*TODO add to parser*)
      | Addf _ -> inc_cmd_no() (*TODO add to parser*)
      | Prover _ -> inc_cmd_no()  
      | Quit -> exit 0
      | _ ->
        error_message (loc cmd)
        (fun ppf -> Format.fprintf ppf 
"@[one@ of@ following@ commands@ expected:@ load@,functionality@,real@,ideal@,addv@,addf@,quit.@]")
      end
    with _ ->
      prompt();
      restart_loop()
  in

  let setup_loop () : unit =
    if (currs()).post_done
    then restart_loop()
    else complete_loop ()
  in

  let rec interpreter_loop (): unit =
    prompt();
    match (currs()).config with
    | Some _ -> done_loop()
    | None -> setup_loop()
    ;
    interpreter_loop()
  in
  
  stack := [];
  stack := init_state::!stack;
  UcEcInterface.init();
  interpreter_loop()
  
let stdIOclient =
  let lexbuf = lexbuf_from_channel "stdin" stdin  in
  interpret lexbuf
  
 
(**)

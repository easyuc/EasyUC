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
  if UcState.get_pg_mode ()
  then UcState.set_pg_start_pos lexbuf.L.lex_curr_p.L.pos_cnum;
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

let fmt = Format.err_formatter

let print_prompt () : unit =
  let str = cmd_prompt (currs()).cmd_no in
  Format.fprintf fmt "%s@." str

let cmd_name () =
  "cmd #"^(string_of_int (currs()).cmd_no)

let pp_uc_file_pos
(fmt : Format.formatter) ( c : interpreter_state) : unit =
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
    let str = "UC file position: "^(l.loc_fname)^" "^b^" "^s^";" in
    Format.fprintf fmt "%s@." str
  | None -> ()
  end

let pp_interpreter_state 
(fmt : Format.formatter) ( c : interpreter_state) : unit =
    match c.config with
    | Some config ->
      Format.fprintf fmt "%a@." 
        pp_config  config;
      begin match c.effect with
      | None -> ()
      | Some eff ->
        Format.fprintf fmt "@.%a@." 
        pp_effect eff;
      end
    | None ->
      match c.config_gen with
      | Some config -> pp_config fmt config
      | None -> 
        match c.maps with
        | Some _ -> 
          let str = "state: uc file "^(Option.get c.root)^" loaded;" in
          Format.fprintf fmt "%s@." str
        | None   ->
          let str = "state: uc file not loaded;" in
          Format.fprintf fmt "%s@." str
   

let interpret (lexbuf : L.lexbuf) =

  let print_state (c : interpreter_state) : unit =
    pp_uc_file_pos fmt c;
    Format.fprintf fmt "state:@.%a;" pp_interpreter_state c
  in
  
  let push_print (is : interpreter_state) : unit =
    push is;
    if (UcState.get_batch_mode ())
    then ()
    else
      print_state is
  in

  let prompt () : unit =
    if (UcState.get_batch_mode ())
    then ()
    else
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
    match maps with
    | Some _ ->
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
      push_print news
    | None -> ()
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
    push_print news
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
    push_print news
  in

  let undo (pi : int located) : unit =
    let i = unloc pi in
    let l = List.length !stack in
    if ((i < l) && (i > 0)) 
    then begin
      stack := BatList.drop i (!stack);
      let c = currs() in
      print_state c
    end else
      error_message (loc pi)
        (fun ppf -> Format.fprintf ppf 
"@[%i@ is@ not@ between@ 1@ and@ %i@]" i (l-1))
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
    push_print news
  in

  let send (sme : sent_msg_expr) : unit =
    let c = currs() in
    let cconfig = Option.get c.config in
    let conf = send_message_to_real_or_ideal_config cconfig sme in
    let news =  
      {
        c with
        cmd_no = c.cmd_no+1;
        ucdsl_new = false;
        post_done = false;
        config = Some conf;
        effect = Some EffectOK;  (* send_message_to_real_or_ideal_config
                                    doesn't produce an effect *)
      } in
    push_print news
  in

  let step (ppio : EcParsetree.pprover_infos option) : unit =
    let c = currs() in
    let cconfig = Option.get c.config in
    let conf, eff =
      step_running_or_sending_real_or_ideal_config cconfig ppio in
    let news =  
      {
        c with
        cmd_no = c.cmd_no+1;
        ucdsl_new = false;
        post_done = false;
        config = Some conf;
        effect = Some eff;
      } in
    push_print news
  in

  let run () : unit =

    let rec runr (conf : config) : config * effect =
      let conf, eff =
        step_running_or_sending_real_or_ideal_config conf None in
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
    push_print news
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
        push_print news
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
        push_print news
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

  let confirm (peff : peffect) : unit =
    let c = currs() in
    let effo = c.effect in
    let pp_effect ppf eff = pp_effect ppf eff in
    begin match effo with
    | None -> 
      error_message (loc peff) (fun ppf -> Format.fprintf ppf 
      "@[assert@ failed@ as@ no@ effects@ occured@ after@ last@ command@, only@ run@ and step@ commands@ produce@ effects.]")
    | Some eff ->
      begin match (unloc peff) with
      | EffectOK ->
        begin match eff with
        | EffectOK -> ()
        | _ ->
          error_message (loc peff) (fun ppf -> Format.fprintf ppf 
      "@[assert@ of@ EffectOK@ failed.@ The@ effect@ that@ occurred:@ %a]"
         pp_effect eff)
        end
      | EffectRand ->
        begin match eff with
        | EffectRand _ -> ()
        | _ -> 
          error_message (loc peff) (fun ppf -> Format.fprintf ppf 
      "@[assert@ of@ EffectRand@ failed.@ The@ effect@ that@ occurred:@ %a]"
         pp_effect eff)
        end
      | EffectMsgOut (sme, ct) ->
        begin match eff with
        | EffectMsgOut (str , ctrl) ->
          let smestr = typecheck_and_pp_sent_msg_expr (Option.get c.config) sme
          in
          if smestr<>str 
          then error_message (loc peff) (fun ppf -> Format.fprintf ppf 
            "@[assert@ of@ EffectMsgOut@ failed.@ The@ message@ that@ was@ sent@
            ,%s is different from the asserted one %s]" str smestr)
          else if ct = UcSpec.CtrlAdv && ctrl = UcInterpreter.CtrlEnv
          then error_message (loc peff) (fun ppf -> Format.fprintf ppf 
             "@[assert@ of@ EffectMsgOut@ failed.@ The@ Env@ has@ control@
              , asserted@ control@ was@ Adv]")
          else if ct = UcSpec.CtrlEnv && ctrl = UcInterpreter.CtrlAdv
          then error_message (loc peff) (fun ppf -> Format.fprintf ppf 
             "@[assert@ of@ EffectMsgOut@ failed.@ The@ Adv@ has@ control@
              , asserted@ control@ was@ Env]")
          else ()
        | _ -> 
          error_message (loc peff) (fun ppf -> Format.fprintf ppf 
      "@[assert@ of@ EffectMsgOut@ failed.@ The@ effect@ that@ occurred:@ %a]"
         pp_effect eff)
        end
      | EffectFailOut ->
        begin match eff with
        | EffectFailOut -> ()
        | _ -> 
          error_message (loc peff) (fun ppf -> Format.fprintf ppf 
      "@[assert@ of@ EffectFailOut@ failed.@ The@ effect@ that@ occurred:@ %a]"
         pp_effect eff)
        end
      | EffectBlockedIf ->
        begin match eff with
        | EffectBlockedIf -> ()
        | _ -> 
         error_message (loc peff) (fun ppf -> Format.fprintf ppf 
      "@[assert@ of@ EffectBlockedIf@ failed.@ The@ effect@ that@ occurred:@ %a]"
         pp_effect eff)
        end
      | EffectBlockedMatch ->
        begin match eff with
        | EffectBlockedMatch -> ()
        | _ -> 
          error_message (loc peff) (fun ppf -> Format.fprintf ppf 
      "@[assert@ of@ EffectBlockedMatch@ failed.@ The@ effect@ that@ occurred:@ %a]"
         pp_effect eff)
        end
      | EffectBlockedPortOrAddrCompare ->
        begin match eff with
        | EffectBlockedPortOrAddrCompare -> ()
        | _ -> 
          error_message (loc peff) (fun ppf -> Format.fprintf ppf 
      "@[assert@ of@ EffectBlockedPortOrAddrCompare@ failed.@ The@ effect@ that@ occurred:@ %a]"
         pp_effect eff)
        end
      end
    end
  in
      

  let rec done_loop (): unit =
    try
      let cmd = next_cmd lexbuf in
      begin  match (unloc cmd) with
      | Send sme  -> send sme
      | Run -> run()
      | Step ppio -> step ppio
      | Addv tb -> addv tb 
      | Addf (psy,pex) -> addf psy pex
      | Prover ppinfo -> prover ppinfo
      | Back pi -> undo pi
      | Finish -> donec()
      | Quit -> exit 0
      | Assert peff -> confirm peff
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
      | Back pi -> undo pi
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
      | Back pi -> undo pi
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
      | Addv tb -> addv tb (*TODO add to parser*)
      | Addf (psy,pex) -> addf psy pex (*TODO add to parser*)
      | Prover ppinfo -> prover ppinfo  

      | World w ->
        world w
      | Back pi -> undo pi
      | Quit -> exit 0
      | _ ->
        error_message (loc cmd)
        (fun ppf -> Format.fprintf ppf "@[addv@,@ addf@,@ prover@,@ or@ world@ command@ expected@]")
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
      | Addv tb -> addv tb (*TODO add to parser*)
      | Addf (psy,pex) -> addf psy pex (*TODO add to parser*)
      | Prover ppinfo -> prover ppinfo
      | Back pi -> undo pi  
      | Quit -> exit 0
      | _ ->
        error_message (loc cmd)
        (fun ppf -> Format.fprintf ppf 
"@[one@ of@ following@ commands@ expected:@ load@,@ functionality@,@ real@,@ ideal@,@ addv@,@ addf@,@ quit.@]")
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
    begin 
    match (currs()).config with
    | Some _ -> done_loop()
    | None -> setup_loop()
    end;
    interpreter_loop()
  in
  
  stack := [];
  stack := init_state::!stack;
  UcEcInterface.init();
  interpreter_loop()
  
let stdIOclient =
  UcState.set_raw_messages();
  let lexbuf = lexbuf_from_channel "stdin" stdin  in
  interpret lexbuf
  
 
(**)

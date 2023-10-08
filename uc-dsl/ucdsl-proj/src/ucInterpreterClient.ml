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
  | None -> 
    let str = "UC file position: None;" in
    Format.fprintf fmt "%s@." str
  end

let pp_effect (ppf : Format.formatter) (e : effect) : unit =
  let pp_control (ppf : Format.formatter) (ctrl : control) : unit =
    match ctrl with
    | CtrlEnv -> Format.fprintf ppf "environment"
    | CtrlAdv -> Format.fprintf ppf "adversary"
  in
  match e with
  | EffectOK                       -> ()
  | EffectRand id                  ->
    Format.fprintf ppf "@[note: random value was assigned to: %s@]" id
  | EffectMsgOut (pp_sme, ctrl)    ->
    Format.fprintf ppf 
    "@[message was output:@ %a:@ %s@]" pp_control ctrl pp_sme
  | EffectFailOut                  -> 
    Format.fprintf ppf "note: \"fail.\" was called."

let pp_interpreter_state 
(fmt : Format.formatter) ( c : interpreter_state) : unit =
  match c.config with
  | Some config ->
    Format.fprintf fmt "%a" pp_config config;
  | None ->
    match c.config_gen with
    | Some config -> 
      Format.fprintf fmt "%a" pp_config config
    | None -> 
      match c.maps with
      | Some _ -> 
        let str = "uc file "^(Option.get c.root)^" loaded" in
        Format.fprintf fmt "%s" str
      | None   ->
        let str = "uc file not loaded" in
        Format.fprintf fmt "%s" str

let interpret (lexbuf : L.lexbuf) =

  let print_state (c : interpreter_state) : unit =
    begin match c.effect with
    | None -> ()
    | Some eff ->
      Format.fprintf fmt "@.effect:@.%a@.;@." 
      pp_effect eff
    end;
    pp_uc_file_pos fmt c;
    Format.fprintf fmt "state:@.%a@.;@." pp_interpreter_state c
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
      begin
     (* Format.fprintf fmt "[warning: this is just a post-drill%i@.;@." (currs()).cmd_no;*)
      print_prompt()
      end
  in

  let load (psym : psymbol) : unit =
    let root = String.capitalize_ascii (unloc psym) in
    EcCommands.ucdsl_new();
    let maps =
    try
      ( UcParseAndTypecheckFile.parse_and_typecheck_file_or_id
        (UcParseFile.FOID_Id psym)) 
    with _ ->
        EcCommands.ucdsl_end();
        error_message (loc psym)
        (fun ppf -> Format.fprintf ppf
          "@[problem@ loading@ file.@ try@ running@ first@ ucdsl -units %s @]" 
          (unloc psym))
    in
    let c = currs() in
    let news = 
      { c with
        cmd_no = c.cmd_no+1;
        ucdsl_new = true;
        post_done = false;
        root = Some root;
        maps = Some maps;
        config_gen = None;
        config = None;
        effect = None;
      } in
    push_print news
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
    if (List.exists (fun is -> is.cmd_no = i) !stack)
    then begin
      stack := List.filter (fun is -> is.cmd_no <= i) (!stack);
      let c = currs() in
      print_state c
    end else
      error_message (loc pi)
        (fun ppf -> Format.fprintf ppf 
           "@[could@ not@ find@ command@ with@ cmd_no@ %i@]" i)
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

  let step_core (loc : EcLocation.t)
      (ppio : EcParsetree.pprover_infos option) : config * effect =
    let c = currs() in
    let cconfig = Option.get c.config in
    let is_running_or_sending_real_or_ideal_config config =
      is_real_running_config config  ||
      is_ideal_running_config config ||
      is_real_sending_config config  ||
      is_ideal_sending_config config in
    if is_running_or_sending_real_or_ideal_config cconfig
    then
      try step_running_or_sending_real_or_ideal_config cconfig
          ppio None with
      | StepBlockedIf                -> 
          error_message loc
          (fun ppf ->
             Format.fprintf ppf
             "@[blocking:@ cannot@ decide@ if@ condition@]")
      | StepBlockedMatch             ->
          error_message loc
          (fun ppf ->
             Format.fprintf ppf
             ("@[blocking:@ cannot@ determine@ datatype@ " ^^
              "constructor@ in@ match@]"))
      | StepBlockedPortOrAddrCompare ->
          error_message loc
          (fun ppf ->
             Format.fprintf ppf
             ("@[blocking:@ cannot@ decide@ port@ or@ address@ " ^^
              "comparisons@]"))
    else
      error_message loc
      (fun ppf ->
         Format.fprintf ppf 
         ("@[you@ can@ step@ through@ only@ when@ running@ code@ or@ " ^^
          "sending@ messages.@]"))
  in

  let step (loc : EcLocation.t)
      (ppio : EcParsetree.pprover_infos option) : unit =
    let conf, eff = step_core loc ppio in  (* could issue error *)
    let c = currs() in
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

  let run (loc : EcLocation.t) : unit =
    let rec runr (conf : config) (eff : effect) : config * effect =
      match try Some  (* so tail recursive *)
                (step_running_or_sending_real_or_ideal_config
                 conf None None) with
            | _ -> None with
      | None             -> conf, eff
      | Some (conf, eff) ->
          (match eff with
           | EffectOK
           | EffectRand _ -> runr conf eff
           | _ -> conf, eff) in
    let conf, eff = step_core loc None in  (* could issue error *)
    let conf, eff =
      match eff with
      | EffectOK
      | EffectRand _ -> runr conf eff
      | _            -> conf, eff in
    let c = currs() in
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
    | None ->
      let cf = Option.get c.config_gen in
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
        error_message (loc peff)
          (fun ppf ->
             Format.fprintf ppf 
             ("@[assert@ failed@ as@ no@ effects@ occured@ after@ last@ " ^^
              "command,@ only@ run@ and step@ commands@ produce@ effects@]"))
    | Some eff ->
        begin match (unloc peff) with
        | EffectOK ->
          begin match eff with
          | EffectOK -> ()
          | _        ->
            error_message (loc peff)
            (fun ppf ->
               Format.fprintf ppf 
               ("@[assert@ of@ OK@ effect failed.@ The@ effect@ that@ " ^^
                "occurred:@ %a@]")
               pp_effect eff)
          end
        | EffectRand ->
            begin match eff with
            | EffectRand _ -> ()
            | _            -> 
              error_message (loc peff)
              (fun ppf ->
                 Format.fprintf ppf 
                 ("@[assert@ of@ rand@ effect@ failed.@ The@ effect@ " ^^
                  "that@ occurred:@ %a@]")
                 pp_effect eff)
        end
        | EffectMsgOut (sme, ct) ->
            begin match eff with
            | EffectMsgOut (str, ctrl) ->
                let smestr =
                  typecheck_and_pp_sent_msg_expr (Option.get c.config) sme in
                if smestr <> str 
                  then error_message (loc peff)
                       (fun ppf ->
                          Format.fprintf ppf 
                          ("@[assert@ of@ msg_out@ effect failed.@ The@ " ^^
                           "message@ that@ was@ sent,@ @[%s@],@ is@ "     ^^
                           "different@ from@ the@ asserted@ one,@ "       ^^
                           "@[%s@]@]")
                          str smestr)
                else if ct = UcSpec.CtrlAdv && ctrl = UcInterpreter.CtrlEnv
                  then error_message (loc peff)
                       (fun ppf ->
                          Format.fprintf ppf 
                          ("@[assert@ of@ msg_out@ effect failed.@ The@ " ^^
                           "environment@ has@ control,@ but@ asserted@ "  ^^
                           "control@ was@ adversary@]"))
                else if ct = UcSpec.CtrlEnv && ctrl = UcInterpreter.CtrlAdv
                  then error_message (loc peff)
                       (fun ppf ->
                          Format.fprintf ppf 
                          ("@[assert@ of@ msg_out@ effect@ failed.@ The@ " ^^
                           "adversary@ has@ control,@ but@ asserted@ "     ^^
                           "control@ was@ environment@]"))
                else ()
            | _ -> 
                error_message (loc peff)
                (fun ppf ->
                   Format.fprintf ppf 
                   ("@[assert@ of@ msg_out@ effect@ failed.@ The@ effect@ " ^^
                    "that occurred:@ %a@]")
                   pp_effect eff)
            end
        | EffectFailOut ->
            begin match eff with
            | EffectFailOut -> ()
            | _ -> 
                error_message (loc peff)
                (fun ppf ->
                   Format.fprintf ppf 
                   ("@[assert@ of@ fail_out@ effect failed.@ The@ " ^^
                    "effect@ that@ occurred:@ %a@]")
                   pp_effect eff)
            end
        end
    end
  in
  
  let debug () : unit =
    if (UcState.get_debugging ())
    then begin
      UcState.unset_debugging ();
      non_loc_warning_message (fun ppf -> Format.fprintf ppf 
      "@[debugging@ messages@ turned@ off.@]")
    end else begin
      UcState.set_debugging ();
      non_loc_warning_message (fun ppf -> Format.fprintf ppf 
      "@[debugging@ messages@ turned@ on.@]")
    end
  in

  let rec loop (body : unit -> unit) : unit =
    try
      body()
    with
    | ErrorMessageExn when UcState.get_pg_mode() ->
        prompt();
        loop body
    | e when UcState.get_pg_mode() ->
        try
          non_loc_error_message
          (fun ppf ->
             Format.fprintf ppf 
             "@[unhandled exception: %s\n%s@]"
             (Printexc.to_string e)
             (Printexc.get_backtrace ()))
        with ErrorMessageExn ->
          prompt();
          loop body
  in

  let done_body () : unit =
    let cmd = next_cmd lexbuf in
    match (unloc cmd) with
    | Send sme          -> send sme
    | Run               -> run (loc cmd)
    | Step ppio         -> step (loc cmd) ppio
    | AddVar tb         -> addv tb 
    | AddAss (psy, pex) -> addf psy pex
    | Prover ppinfo     -> prover ppinfo
    | Undo pi           -> undo pi
    | Finish            -> donec ()
    | Quit              -> exit 0
    | Assert peff       -> confirm peff
    | Debug             -> debug ()
    | _                 ->
        error_message (loc cmd)
        (fun ppf ->
           Format.fprintf ppf 
           ("@[one@ of@ following@ commands@ expected:@ send,@ run,@ " ^^
            "step,@ var,@ assumption,@ prover,@ finish@]"))
  in

  let done_loop (): unit =
    loop done_body
  in

  let load_body () : unit =
    let cmd = next_cmd lexbuf in
    match (unloc cmd) with
    | Load psym -> load psym
    | Undo pi   -> undo pi
    | Quit      -> exit 0
    | Debug     -> debug ()
    | _         ->
      error_message (loc cmd)
      (fun ppf -> Format.fprintf ppf "@[load@ command@ expected@]")
  in

  let load_loop () : unit =
    loop load_body
  in

  let funexp_body () : unit =
    let cmd = next_cmd lexbuf in
    match (unloc cmd) with
    | FunEx fe -> funexp fe
    | Undo pi  -> undo pi
    | Quit     -> exit 0
    | Debug    -> debug ()
    | _        ->
        error_message (loc cmd)
        (fun ppf -> Format.fprintf ppf "@[functionality@ command@ expected@]")
  in

  let funexp_loop () : unit = 
    loop funexp_body
  in

  let world_body () : unit =
    let cmd = next_cmd lexbuf in 
    match (unloc cmd) with
    | AddVar tb         -> addv tb
    | AddAss (psy, pex) -> addf psy pex
    | Prover ppinfo     -> prover ppinfo  
    | World w           -> world w
    | Undo pi           -> undo pi
    | Quit              -> exit 0
    | Debug             -> debug ()
    | _                 ->
      error_message (loc cmd)
      (fun ppf ->
         Format.fprintf ppf
         "@[var,@ assumption,@ prover,@ real,@ or@ ideal@ command@ expected@]")
  in

  let world_loop () : unit=
    loop world_body
  in

  let complete_loop () : unit =
    let c = currs() in
    match c.maps with
    | None   -> load_loop()
    | Some _ ->
      match c.config_gen with
      | None   -> funexp_loop ()
      | Some _ -> world_loop ()
  in
 
  let restart_body () : unit =
    let cmd = next_cmd lexbuf in
    match (unloc cmd) with
    | Load psym         -> load psym
    | FunEx fe          -> funexp fe
    | World w           -> world w
    | AddVar tb         -> addv tb
    | AddAss (psy, pex) -> addf psy pex
    | Prover ppinfo     -> prover ppinfo
    | Undo pi           -> undo pi  
    | Quit              -> exit 0
    | Debug             -> debug ()
    | _                 ->
      error_message (loc cmd)
      (fun ppf -> Format.fprintf ppf 
         ("@[one@ of@ following@ commands@ expected:@ load,@ " ^^
          "functionality,@ real,@ ideal,@ var,@ assumption@]"))
  in
      
  let restart_loop () : unit =
    loop restart_body
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
      | None   -> setup_loop()
    end;
    interpreter_loop()
  in
  
  stack := [];
  stack := init_state::!stack;
  UcEcInterface.init();
  interpreter_loop()
  
let stdIOclient () =
  UcState.set_units();
  UcState.set_pg_mode();
  let lexbuf = lexbuf_from_channel "stdin" stdin  in
  interpret lexbuf

let file_client (file : string) =
  UcState.set_units();
  let ch = open_in file in
  let lexbuf = lexbuf_from_channel file ch in
  interpret lexbuf;
  close_in ch

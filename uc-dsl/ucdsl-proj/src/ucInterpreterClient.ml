(* UcInterpreterClient module *)

open EcParsetree
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

let lexbuf_from_string (name : string) (str : string) =
  let lexbuf = L.from_string ~with_positions:true str in
  reset_pos_rename lexbuf name;
  lexbuf

let file_str : string ref = ref ""

let fmt = Format.err_formatter

let echo_cmd (pos_start : L.position) (pos_end : L.position) : unit =
  if (UcState.get_pg_mode ()) || (UcState.get_batch_mode ())
  then ()
  else
    let p1 = pos_start.L.pos_cnum in
    let p2 = pos_end.L.pos_cnum in
    let cmd = String.sub !file_str p1 (p2-p1)  in
    Format.fprintf fmt "%s@." cmd


let next_cmd (lexbuf : L.lexbuf) : interpreter_command =
  if UcState.get_pg_mode ()
  then UcState.set_pg_start_pos lexbuf.L.lex_curr_p.L.pos_cnum;
  let pos_before_read = lexbuf.L.lex_curr_p in
  let intcom =
    try UcParser.interpreter_command read lexbuf
    with
    | UcParser.Error ->
       let pos_after_read = lexbuf.L.lex_curr_p in
       echo_cmd pos_before_read pos_after_read;
      (error_message  (* no need to close channel *)
       (EcLocation.make lexbuf.L.lex_start_p lexbuf.L.lex_curr_p)
       (fun ppf -> Format.fprintf ppf "@[parse@ error@]"))
  in
  let pos_after_read = lexbuf.L.lex_curr_p in
  echo_cmd pos_before_read pos_after_read;
  intcom

type interpreter_state =
  {
    cmd_no     : int;
    ucdsl_new  : bool;
    post_done  : bool;
    root       : string option;
    maps       : maps_tyd option;
    config_gen : config option;
    config     : config option;
    effect     : effect option
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
    let b,s = (string_of_int (l.loc_bchar+1)),(string_of_int (l.loc_echar+1)) in
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
    if (UcState.get_batch_mode ())
    then ()
    else begin
      begin match c.effect with
      | None     -> ()
      | Some eff ->
        Format.fprintf fmt "@.effect:@.%a@.;@."
        pp_effect eff
      end;
      pp_uc_file_pos fmt c;
      Format.fprintf fmt "state:@.%a@.;@." pp_interpreter_state c
    end
  in

  let push_print (is : interpreter_state) : unit =
    push is;
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
    let root = unloc psym in  (* capitalized, because uident in parser *)
    UcStackedScopes.new_scope ();
    let pg_mode = UcState.get_pg_mode () in
    (* if we're in pg_mode, temporarily revert to ordinary error/warning
       messages, while we parse and typecheck file *)
    let () = if pg_mode then UcState.unset_pg_mode () in
    let maps =
      try
        UcParseAndTypecheckFile.parse_and_typecheck_file_or_id
        (UcParseFile.FOID_Id psym)
      with e when e <> Sys.Break ->
        if pg_mode then UcState.set_pg_mode ();
        UcStackedScopes.end_scope_ignore();
        error_message (loc psym)
        (fun ppf -> Format.fprintf ppf
          ("@[problem@ loading@ file.@ try@ running@ first@ ucdsl " ^^
           "-units %s@]")
        (unloc psym)) in
    let () = if pg_mode then UcState.set_pg_mode () in
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
      let dos, undos = List.partition (fun is -> is.cmd_no <= i) (!stack) in
      stack := dos;
      let undo_loads = List.filter (fun is -> is.ucdsl_new) undos in
      List.iter (fun _ -> UcStackedScopes.end_scope_ignore ()) undo_loads;
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

  let send (loc : EcLocation.t) (sme : sent_msg_expr) : unit =
    let c = currs() in
    let cconfig = Option.get c.config in
    if is_real_config cconfig || is_ideal_config cconfig
    then
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
    else
      error_message loc
      (fun ppf ->
         Format.fprintf ppf
           ("@[you@ can@ send@ messages@ only@ when@ " ^^
             "environment@ or@ adverary@ have@ control"))
  in

  let step_core (loc : EcLocation.t)
      (ppio : EcParsetree.pprover_infos option) (mdbso : mod_dbs option)
        : config * effect =
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
          ppio mdbso with
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

  let step (loc : EcLocation.t) (ppio : EcParsetree.pprover_infos option)
      (mpdbso : mod_dbs option) : unit =
    let conf, eff = step_core loc ppio mpdbso in  (* could issue error *)
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

  let run (loc : EcLocation.t) (stepno : int option) : unit =
    let decstepno (stepno : int option) : int option =
      match stepno with
      | None -> None
      | Some i -> Some (i-1)
    in
    let proceed (stepno : int option) : bool =
      match stepno with
      | None -> true
      | Some i -> i > 0
    in
    let rec runr (conf : config) (eff : effect) (stepno : int option)
            : config * effect =
      if (UcState.get_run_print_pos ())
      then begin
        let c = currs() in
        let c' =
        {
          c with
          ucdsl_new = false;
          post_done = false;
          config = Some conf;
          effect = Some eff;
        } in
        pp_uc_file_pos fmt c'
        end;
      if proceed stepno
      then
        match try Some  (* so tail recursive *)
                  (step_running_or_sending_real_or_ideal_config
                   conf None None) with
              | e when e <> Sys.Break -> None with
        | None             -> conf, eff
        | Some (conf, eff) ->
            (match eff with
             | EffectOK
             | EffectRand _ -> runr conf eff (decstepno stepno)
             | _ -> conf, eff)
      else conf, eff
    in
    if proceed stepno
    then
      let conf, eff = step_core loc None None in  (* could issue error *)
      let conf, eff =
        match eff with
        | EffectOK
        | EffectRand _ -> runr conf eff (decstepno stepno)
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
    else ()
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

  let add_var (tb : type_binding) : unit =
    let mdfy cf = add_var_to_config cf tb.id tb.ty in
    modify_config mdfy
  in

  let add_ass (psy : psymbol) (pex : pformula) : unit =
    let mdfy cf = add_hyp_to_config cf psy pex in
    modify_config mdfy
  in

  let prover (ppinfo : EcParsetree.pprover_infos) : unit =
    let mdfy cf = update_prover_infos_config cf ppinfo in
    modify_config mdfy
  in

  let hint (mdbs: mod_dbs) : unit =
    let mdfy cf = modify_rewriting_dbs_config cf mdbs in
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
            | EffectOK ->
              error_message (loc peff)
              (fun ppf ->
                 Format.fprintf ppf
                 ("@[assert@ of@ rand@ effect@ failed.@ The@ effect@ " ^^
                  "that@ occurred:@ OK@]"))
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
            | EffectOK ->
              error_message (loc peff)
              (fun ppf ->
                 Format.fprintf ppf
                 ("@[assert@ of@ msg_out@ effect@ failed.@ The@ effect@ " ^^
                  "that@ occurred:@ OK@]"))
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
            | EffectOK ->
              error_message (loc peff)
              (fun ppf ->
                 Format.fprintf ppf
                 ("@[assert@ of@ fail_out@ effect@ failed.@ The@ effect@ " ^^
                  "that@ occurred:@ OK@]"))
            | _ ->
                error_message (loc peff)
                (fun ppf ->
                   Format.fprintf ppf
                   ("@[assert@ of@ fail_out@ effect failed.@ The@ " ^^
                    "effect@ that@ occurred:@ %a@]")
                   pp_effect eff)
            end
        end
    end;
    print_state c
  in

  let debug () : unit =
    if (UcState.get_debugging ())
    then begin
      UcState.unset_debugging ();
      non_loc_warning_message (fun ppf -> Format.fprintf ppf
      "@[debugging@ messages@ turned@ off@]")
    end else begin
      UcState.set_debugging ();
      non_loc_warning_message (fun ppf -> Format.fprintf ppf
      "@[debugging@ messages@ turned@ on@ (see@ buffer@ *trace*)@]")
    end
  in

  let pg_mode_break_handler () : unit =
    try
      non_loc_error_message (fun ppf -> Format.fprintf ppf ("interrupted."));
    with ErrorMessageExn -> ()
  in

  let rec loop (body : unit -> unit) : unit =
    try
      body()
    with
    | ErrorMessageExn when UcState.get_pg_mode() ->
        prompt();
        loop body
    | Sys.Break when UcState.get_pg_mode() ->
        pg_mode_break_handler ();
        prompt();
        loop body
    | Stack_overflow -> (*issue #56: print graceful error message*)
       let print_stack_overflow_message ppf =
         Format.fprintf ppf
   "@[stack overflow, check your EasyCrypt rewriting and simplification hints@]"
       in
       if UcState.get_pg_mode()
       then
         try
          non_loc_error_message print_stack_overflow_message
         with ErrorMessageExn ->
         begin
          prompt();
          loop body
         end
       else
         non_loc_error_message_exit print_stack_overflow_message
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
    | Send sme           -> send (loc cmd) sme
    | Run no             -> run (loc cmd) no
    | Step (ppio, mdbso) -> step (loc cmd) ppio mdbso
    | AddVar tb          -> add_var tb
    | AddAss (psy, pex)  -> add_ass psy pex
    | Prover ppinfo      -> prover ppinfo
    | Hint mod_pdbs      -> hint mod_pdbs
    | Undo pi            -> undo pi
    | Finish             -> donec ()
    | Quit               -> exit 0
    | Assert peff        -> confirm peff
    | Debug              -> debug ()
    | _                  ->
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
    | AddVar tb         -> add_var tb
    | AddAss (psy, pex) -> add_ass psy pex
    | Prover ppinfo     -> prover ppinfo
    | Hint mod_pdbs     -> hint mod_pdbs
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
    | AddVar tb         -> add_var tb
    | AddAss (psy, pex) -> add_ass psy pex
    | Prover ppinfo     -> prover ppinfo
    | Hint mod_pdbs     -> hint mod_pdbs
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
    begin try
      prompt();
      match (currs()).config with
      | Some _ -> done_loop()
      | None   -> setup_loop()
    with Sys.Break when UcState.get_pg_mode() ->
      pg_mode_break_handler ()
    end;
    interpreter_loop()
  in

  stack := [];
  stack := init_state :: !stack;
  interpreter_loop()

let std_IO_client () =
  UcState.set_pg_mode();
  Sys.catch_break true;
  let lexbuf = lexbuf_from_channel "stdin" stdin  in
  interpret lexbuf

let file_client (file : string) =
  let read_whole_file filename =
    let ch = open_in_bin filename in
    let s = really_input_string ch (in_channel_length ch) in
    close_in ch;
    s
  in
  UcState.unset_pg_mode();
  file_str := read_whole_file file;
  let lexbuf = lexbuf_from_string file !file_str in
  interpret lexbuf

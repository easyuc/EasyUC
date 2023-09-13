open UcInterpreter

let parse_error_handling lexbuf =
 UcMessage.error_message  (* no need to close channel *)
 (EcLocation.make lexbuf.Lexing.lex_start_p lexbuf.Lexing.lex_curr_p)
 (fun ppf -> Format.fprintf ppf "@[parse@ error@]")

let parse_sent_msg_expr (sme : string) : UcSpec.sent_msg_expr =
  let lexbuf = Lexing.from_string sme in
  try UcParser.sent_msg_expr_start UcLexer.read lexbuf with
  | UcParser.Error -> parse_error_handling lexbuf

let parse_fun_expr (fe : string) : UcSpec.fun_expr =
  let lexbuf = Lexing.from_string fe in
  try UcParser.fun_expr_start UcLexer.read lexbuf  with
  | UcParser.Error -> parse_error_handling lexbuf

let test_gen_config (include_dirs : string list) (file : string)
    (fun_ex : string) : unit =
  UcEcInterface.init ();
  UcState.set_units();
  UcState.set_include_dirs include_dirs;
  let maps =
    UcParseAndTypecheckFile.parse_and_typecheck_file_or_id (FOID_File file) in
  let root = UcUtils.capitalized_root_of_filename_with_extension file in
  let env = UcEcInterface.env () in
  let fun_expr = parse_fun_expr fun_ex in
  let config = create_gen_config root maps env fun_expr in
  pp_config Format.std_formatter config

let test_real_config (include_dirs : string list) (file : string)
    (fun_ex : string) : unit =
  UcEcInterface.init ();
  UcState.set_units();
  UcState.set_include_dirs include_dirs;
  let maps =
    UcParseAndTypecheckFile.parse_and_typecheck_file_or_id (FOID_File file) in
  let root = UcUtils.capitalized_root_of_filename_with_extension file in
  let env = UcEcInterface.env () in
  let fun_expr = parse_fun_expr fun_ex in
  let config = create_gen_config root maps env fun_expr in
  let config = real_of_gen_config config in
  pp_config Format.std_formatter config

let test_ideal_config (include_dirs : string list) (file : string)
    (fun_ex : string) : unit =
  UcEcInterface.init ();
  UcState.set_units();
  UcState.set_include_dirs include_dirs;
  let maps =
    UcParseAndTypecheckFile.parse_and_typecheck_file_or_id (FOID_File file) in
  let root = UcUtils.capitalized_root_of_filename_with_extension file in
  let env = UcEcInterface.env () in
  let fun_expr = parse_fun_expr fun_ex in
  let config = create_gen_config root maps env fun_expr in
  let config = ideal_of_gen_config config in
  pp_config Format.std_formatter config

let test_sent_real_config_core
    (config : config) (sme : UcSpec.sent_msg_expr) : unit =
  let () = pp_config Format.err_formatter config in
  Format.pp_print_newline Format.err_formatter ();
  let () = Printf.eprintf "---\n" in
  let config = send_message_to_real_or_ideal_config config sme in
  let () = pp_config Format.err_formatter config in
  Format.pp_print_newline Format.err_formatter ();
  let () = Printf.eprintf "---\n" in
  let (config, eff) =
    step_running_or_sending_real_or_ideal_config config None in
  let () = pp_config Format.err_formatter config in
  Format.pp_print_newline Format.err_formatter ();
  let () = Printf.eprintf "---\n" in
  pp_effect Format.err_formatter eff;
  Format.pp_print_newline Format.err_formatter ()

let test_sent_real_config_core_cont
    (config : config) (sme : UcSpec.sent_msg_expr) : config =
  let () = pp_config Format.err_formatter config in
  Format.pp_print_newline Format.err_formatter ();
  let () = Printf.eprintf "---\n" in
  let config = send_message_to_real_or_ideal_config config sme in
  let () = pp_config Format.err_formatter config in
  Format.pp_print_newline Format.err_formatter ();
  let () = Printf.eprintf "---\n" in
  let (config, eff) =
    step_running_or_sending_real_or_ideal_config config None in
  let () = pp_config Format.err_formatter config in
  Format.pp_print_newline Format.err_formatter ();
  let () = Printf.eprintf "---\n" in
  pp_effect Format.err_formatter eff;
  Format.pp_print_newline Format.err_formatter ();
  config

let test_sent_real_config_1 (include_dirs : string list) (file : string)
    (fun_ex : string) : unit =
  UcEcInterface.init ();
  UcState.set_units();
  UcState.set_include_dirs include_dirs;
  UcState.set_debugging ();
  let maps =
    UcParseAndTypecheckFile.parse_and_typecheck_file_or_id (FOID_File file) in
  let root = UcUtils.capitalized_root_of_filename_with_extension file in
  let env = UcEcInterface.env () in
  let fun_expr = parse_fun_expr fun_ex in
  let config = create_gen_config root maps env fun_expr in
  let real_config = real_of_gen_config config in
  let sme =
   parse_sent_msg_expr
   "((env_root_addr, 1))@SMC2.SMC2Dir.Pt1.smc_req(T.port_y,T.testtext)@((func,1))" in
  test_sent_real_config_core real_config sme

let test_sent_real_config_1a (include_dirs : string list) (file : string)
    (fun_ex : string) : unit =
  UcEcInterface.init ();
  UcState.set_units();
  UcState.set_include_dirs include_dirs;
  UcState.set_debugging ();
  let maps =
    UcParseAndTypecheckFile.parse_and_typecheck_file_or_id (FOID_File file) in
  let root = UcUtils.capitalized_root_of_filename_with_extension file in
  let env = UcEcInterface.env () in
  let fun_expr = parse_fun_expr fun_ex in
  let config = create_gen_config root maps env fun_expr in
  let real_config = real_of_gen_config config in
  let sme =
   parse_sent_msg_expr
   "((env_root_addr, 1))@SMC2.SMC2Dir.Pt1.smc_req(T.port_y,T.testtext)@((func ++ [1], 1))" in
  test_sent_real_config_core real_config sme

let test_sent_real_config_2 (include_dirs : string list) (file : string)
    (fun_ex : string) : unit =
  UcEcInterface.init ();
  UcState.set_units();
  UcState.set_include_dirs include_dirs;
  UcState.set_debugging ();
  let maps =
    UcParseAndTypecheckFile.parse_and_typecheck_file_or_id (FOID_File file) in
  let root = UcUtils.capitalized_root_of_filename_with_extension file in
  let env = UcEcInterface.env () in
  let fun_expr = parse_fun_expr fun_ex in
  let config = create_gen_config root maps env fun_expr in
  let real_config = real_of_gen_config config in
  let sme =
   parse_sent_msg_expr
   "((env_root_addr, 1))@_@((adv, 22))" in
  test_sent_real_config_core real_config sme

let test_sent_real_config_3 (include_dirs : string list) (file : string)
    (fun_ex : string) : unit =
  UcEcInterface.init ();
  UcState.set_units();
  UcState.set_include_dirs include_dirs;
  UcState.set_debugging ();
  let maps =
    UcParseAndTypecheckFile.parse_and_typecheck_file_or_id (FOID_File file) in
  let root = UcUtils.capitalized_root_of_filename_with_extension file in
  let env = UcEcInterface.env () in
  let fun_expr = parse_fun_expr fun_ex in
  let config = create_gen_config root maps env fun_expr in
  let real_config = real_of_gen_config config in
  let sme =
   parse_sent_msg_expr
   "(([], 1))@_@((adv, 9))" in
  test_sent_real_config_core real_config sme

let test_sent_real_config_4 (include_dirs : string list) (file : string)
    (fun_ex : string) : unit =
  UcEcInterface.init ();
  UcState.set_units();
  UcState.set_include_dirs include_dirs;
  UcState.set_debugging ();
  let maps =
    UcParseAndTypecheckFile.parse_and_typecheck_file_or_id (FOID_File file) in
  let root = UcUtils.capitalized_root_of_filename_with_extension file in
  let env = UcEcInterface.env () in
  let fun_expr = parse_fun_expr fun_ex in
  let config = create_gen_config root maps env fun_expr in
  let () = pp_config Format.err_formatter config in
  Format.pp_print_newline Format.err_formatter ();
  let () = Printf.eprintf "---\n" in
  let real_config = real_of_gen_config config in
  let sme =
   parse_sent_msg_expr
   "((env_root_addr, 1))@_@((adv, 22))" in
  let real_config = test_sent_real_config_core_cont real_config sme in
(*
  let sme =
   parse_sent_msg_expr
   "((adv, 1))@_@((env_root_addr, 1))" in
*)
  let sme =
   parse_sent_msg_expr
   "((adv, 5))@SMC.KEDir.Pt1.pong@((func ++ [1], 1))" in
  test_sent_real_config_core real_config sme

(* include dirs not used when opening file! 
test has to be run in directory that contains SMC.uc file!*)

let smc2_dir = "~/EasyUC/uc-dsl/examples/smc2"
let smc2 = "SMC2.uc"

let smc2_dir_ping = "~/EasyUC/uc-dsl/examples/smc2-ping-adv"
let smc2 = "SMC2.uc"

let test_gen_config_1 (): unit =
  let fe = "SMC2.SMC2Real(SMC.SMCReal(KeyExchange.KEReal), SMC.SMCReal(KeyExchange.KEReal))" in
  test_gen_config [smc2_dir] smc2 fe

let test_gen_config_2 (): unit =
  let fe = "SMC2.SMC2Real(SMC.SMCReal(KeyExchange.KEIdeal), SMC.SMCReal(KeyExchange.KEReal))" in
  test_gen_config [smc2_dir] smc2 fe

let test_real_config_1 (): unit =
  let fe = "SMC2.SMC2Real(SMC.SMCReal(KeyExchange.KEReal), SMC.SMCReal(KeyExchange.KEReal))" in
  test_real_config [smc2_dir] smc2 fe

let test_real_config_2 (): unit =
  let fe = "SMC2.SMC2Real(SMC.SMCReal(KeyExchange.KEIdeal), SMC.SMCReal(KeyExchange.KEReal))" in
  test_real_config [smc2_dir] smc2 fe

let test_ideal_config_1 (): unit =
  let fe = "SMC2.SMC2Real(SMC.SMCReal(KeyExchange.KEReal), SMC.SMCReal(KeyExchange.KEReal))" in
  test_ideal_config [smc2_dir] smc2 fe

let test_ideal_config_2 (): unit =
  let fe = "SMC2.SMC2Real(SMC.SMCReal(KeyExchange.KEIdeal), SMC.SMCReal(KeyExchange.KEReal))" in
  test_ideal_config [smc2_dir] smc2 fe

let test_sent_real_config_1 (): unit =
  let fe = "SMC2.SMC2Real(SMC.SMCReal(KeyExchange.KEReal), SMC.SMCReal(KeyExchange.KEReal))" in
  test_sent_real_config_1 [smc2_dir] smc2 fe

let test_sent_real_config_1a (): unit =
  let fe = "SMC2.SMC2Real(SMC.SMCReal(KeyExchange.KEReal), SMC.SMCReal(KeyExchange.KEReal))" in
  test_sent_real_config_1a [smc2_dir] smc2 fe

let test_sent_real_config_2 (): unit =
  let fe = "SMC2.SMC2Real(SMC.SMCReal(KeyExchange.KEReal), SMC.SMCReal(KeyExchange.KEReal))" in
  test_sent_real_config_2 [smc2_dir] smc2 fe

let test_sent_real_config_3 (): unit =
  let fe = "SMC2.SMC2Real(SMC.SMCReal(KeyExchange.KEReal), SMC.SMCReal(KeyExchange.KEReal))" in
  test_sent_real_config_3 [smc2_dir] smc2 fe

let test_sent_real_config_4 (): unit =
(*
  let fe = "SMC2.SMC2Real(SMC.SMCReal(KeyExchange.KEReal), SMC.SMCReal(KeyExchange.KEReal))" in
*)
  let fe = "SMC2.SMC2Real(SMC.SMCReal(KeyExchange.KEIdeal), SMC.SMCReal(KeyExchange.KEReal))" in
  test_sent_real_config_4 [smc2_dir_ping] smc2 fe

(*********)

 
let test_sent_msg_expr (include_dirs : string list) (file : string) (msg_ex : string) : unit =
  UcEcInterface.init ();
  UcState.set_units();
  UcState.set_include_dirs include_dirs;
  let maps = UcParseAndTypecheckFile.parse_and_typecheck_file_or_id (FOID_File file) in
  let env = UcEcInterface.env() in
  let sme = parse_sent_msg_expr msg_ex in
  let smet = UcTypecheck.inter_check_sent_msg_expr maps env sme in
  UcTypedSpec.pp_sent_msg_expr_tyd env Format.std_formatter smet
  
let test_sent_msg_expr0_neg () : unit =
  let me = 
"(if true then port_x else port_x)@SMC2.SMC2Pt1.smc_req(port_x,testtext)$(if true then addr_x else addr_x)" in
  test_sent_msg_expr [smc2_dir] smc2 me

let test_sent_msg_expr0_pos () : unit =
  let me = 
"(port_x)@SMC2.SMC2Pt1.smc_req(port_x,testtext)@(port_x)" in
  test_sent_msg_expr [smc2_dir] smc2 me

(*********)
  
let () =
  let () = Format.set_margin 78 in
  let n = Format.get_margin() in
  Printf.eprintf "margin: %d\n\n" n;
(*
  test_gen_config_1 ();
  print_newline ();
  test_gen_config_2 ();
  print_newline ();
  test_real_config_1 ();
  print_newline ();
  test_real_config_2 ();
  print_newline ();
  test_ideal_config_1 ();
  print_newline ();
  test_ideal_config_2 ();
  print_newline ();
*)


(*
  test_sent_real_config_1 ();
  Printf.eprintf "\n";
*)

(*
  test_sent_real_config_1a ();
  Printf.eprintf "\n";
*)

(*
  test_sent_real_config_2 ();
  Printf.eprintf "\n";
*)


(*
  test_sent_real_config_3 ();
  Printf.eprintf "\n";
*)

  test_sent_real_config_4 ();
  Printf.eprintf "\n";

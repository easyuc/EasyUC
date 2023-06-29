open UcInterpreter

let rf0 = (("Root1","RF"), 1)
let rf1 = (("Root2","RF"), 10)
let rf2 = (("Root3","RF"), 15)

let rw1 = ((fst rf1),(snd rf1),[])
let rw2 = ((fst rf2),(snd rf2),[])
let rw0 = ((fst rf0),(snd rf0),[(RWA_Real rw1);(RWA_Real rw2)])

let if0 = (("Root1","IF"), 1)

let sim0 = (("Root1","Sim"), 1)
let sim2 = (("Root3","Sim"), 15)
let sim1 = (("Root2","Sim"), 10)

let iw =
{
  iw_ideal_func = if0;
  iw_main_sim = sim0;
  iw_other_sims = [sim2;sim1]
}

let w =
{
  worlds_real = rw0;
  worlds_ideal = iw;
}

let test_worlds_pp_0 () =
  pp_worlds Format.std_formatter w
  
(********)

let parse_error_handling lexbuf =
 UcMessage.error_message  (* no need to close channel *)
 (EcLocation.make lexbuf.Lexing.lex_start_p lexbuf.Lexing.lex_curr_p)
 (fun ppf -> Format.fprintf ppf "@[parse@ error@]")

let parse_fun_expr (fe : string) : UcSpec.fun_expr =
  let lexbuf = Lexing.from_string fe in
  try UcParser.fun_expr_start UcLexer.read lexbuf  with
  | UcParser.Error -> parse_error_handling lexbuf

let test_fun_expr_to_worlds (include_dirs : string list) (file : string) (fun_ex : string) : unit =
  UcEcInterface.init ();
  UcState.set_units();
  UcState.set_include_dirs include_dirs;
  let maps = UcParseAndTypecheckFile.parse_and_typecheck_file_or_id (FOID_File file) in
  let root = UcUtils.capitalized_root_of_filename_with_extension file in
  let fun_expr = parse_fun_expr fun_ex in
  let w = fun_expr_to_worlds root maps fun_expr in
  pp_worlds Format.std_formatter w

(* include dirs not used when opening file! 
test has to be run in directory that contains SMC.uc file!*)
let smc_dir = "~/EasyUC/uc-dsl/examples/smc-case-study"
let smc = "SMC.uc"

let test_fun_expr_to_worlds_0 (): unit =
  let fe = "SMC.SMCReal(KeyExchange.KEReal())" in
  test_fun_expr_to_worlds [smc_dir] smc fe

let smc2_dir = "~/EasyUC/uc-dsl/examples/smc2"
let smc2 = "SMC2.uc"

let test_fun_expr_to_worlds_1 (): unit =
  let fe = "SMC2.SMC2Real(SMC.SMCReal(KeyExchange.KEReal), SMC.SMCReal(KeyExchange.KEReal))" in
  test_fun_expr_to_worlds [smc2_dir] smc2 fe

(*********)

let parse_sent_msg_expr (sme : string) : UcSpec.sent_msg_expr =
  let lexbuf = Lexing.from_string sme in
  try UcParser.sent_msg_expr_start UcLexer.read lexbuf with
  | UcParser.Error -> parse_error_handling lexbuf
 
let test_sent_msg_expr (include_dirs : string list) (file : string) (msg_ex : string) : unit =
  UcEcInterface.init ();
  UcState.set_units();
  UcState.set_include_dirs include_dirs;
  let maps = UcParseAndTypecheckFile.parse_and_typecheck_file_or_id (FOID_File file) in
  let env = UcEcInterface.env() in
  let sme = parse_sent_msg_expr msg_ex in
  let smet = UcTypecheck.inter_check_sent_msg_expr maps env sme in
  pp_sent_msg_expr_tyd Format.std_formatter smet
  
let test_sent_msg_expr0_neg () : unit =
  let me = 
"(port_x)@SMC2.SMC2Pt1.smc_req(port_x,testtext)$(addr_x)" in
  test_sent_msg_expr [smc2_dir] smc2 me

let test_sent_msg_expr0_pos () : unit =
  let me = 
"(port_x)@SMC2.SMC2Pt1.smc_req(port_x,testtext)@(port_x)" in
  test_sent_msg_expr [smc2_dir] smc2 me

(*********)
  
let () =
  let () = Format.set_margin 78 in
  let n = Format.get_margin() in
  Printf.printf "margin: %d\n\n" n;
  test_worlds_pp_0 ();
  print_endline "";
  test_fun_expr_to_worlds_0 ();
  print_endline "";
  test_fun_expr_to_worlds_1 ();
  print_endline "";
  test_sent_msg_expr0_pos ();
  print_endline "";
  test_sent_msg_expr0_neg ();
  print_endline ""

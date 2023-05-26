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
  try UcParser.fun_expr UcLexer.read lexbuf  with
  | UcParser.Error -> parse_error_handling lexbuf

let test_fun_expr_to_worlds (include_dirs : string list) (file : string) (fun_ex : string) : unit =
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

(*********)

let parse_sent_msg_expr (sme : string) : UcSpec.sent_msg_expr =
  let lexbuf = Lexing.from_string sme in
  try UcParser.sent_msg_expr UcLexer.read lexbuf  with
  | UcParser.Error -> parse_error_handling lexbuf

  
let () =
  test_worlds_pp_0 ();
  print_endline "";
  UcEcInterface.init ();
  test_fun_expr_to_worlds_0 ();
  print_endline ""

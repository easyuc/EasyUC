open UcEcHypothesisSerialization
open UcEcFormEval

let printEvalResult (res : UcEcFormEval.eval_condition_result) : unit =
  match res with
  | Bool true  -> print_endline "TRUE"
  | Bool false -> print_endline "FALSE"
  | Undecided  -> print_endline "UNDECIDED"
  
let printFormula env (form : EcCoreFol.form) : unit =
  Format.eprintf "%a@."
    (EcPrinting.pp_form (EcPrinting.PPEnv.ofenv env)) 
    (form)

let printPath (path : EcPath.path) : unit =
 Format.eprintf "%a@." EcPrinting.pp_path path

(*copied from UcEcHypothesisSerialization*)
let parse_trans_frm (env : EcEnv.env) (frm_str : string) : EcCoreFol.form =
  let lexbuf = Lexing.from_string frm_str in  
  let pexpr =
    try 
      UcParser.expr_start UcLexer.read lexbuf
    with
    | UcParser.Error ->
      (UcMessage.error_message  (* no need to close channel *)
       (EcLocation.make lexbuf.Lexing.lex_start_p lexbuf.Lexing.lex_curr_p)
       (fun ppf -> Format.fprintf ppf "@[parse@ error@]"))
  in
  let ue  = EcTyping.transtyvars env (EcLocation._dummy, None) in
  let expr,_ = UcTransTypesExprs.transexp env ue pexpr in
  let ff = EcCoreFol.form_of_expr EcFol.mhr expr in
  let ts = EcTypes.Tuni.subst (EcUnify.UniEnv.close ue) in
  let fs = EcFol.Fsubst.f_subst_init ~sty:ts () in
  EcFol.Fsubst.f_subst fs ff

let p_t_concl (hyps : EcEnv.LDecl.hyps) (concl : string) : EcCoreFol.form =
  let env = EcEnv.LDecl.toenv hyps in
  parse_trans_frm env concl
  
let p_t_goal (json_hyps : string) (concl_str : string) : EcEnv.LDecl.hyps * EcCoreFol.form =
  print_endline "json_hyps2ldecl_hyps";
  let hyps = json_hyps2ldecl_hyps json_hyps in
  print_endline "p_t_concl";
  let concl = p_t_concl hyps concl_str in
  hyps, concl

let dft_pi = { 
    EcProvers.dft_prover_infos with 
      pr_provers = 
      List.filter EcProvers.is_prover_known EcProvers.dft_prover_names
  }

(*rewriting dbs copied from ucInterpreter.ml*)
type rewriting_dbs = EcSymbols.qsymbol list

let default_rewriting_dbs = [
  (["Top"; "UCEncoding"],   "epdp");
  (["Top"; "UCBasicTypes"], "ucdsl_interpreter_hints")
  ]

let lemmas_of_rewriting_dbs (env : EcEnv.env) (dbs : rewriting_dbs)
      : EcPath.path list =
  let lemmas_of_rw_dbs (db : EcSymbols.qsymbol) : EcPath.path list =
    let lems = snd (EcEnv.BaseRw.lookup db env) in
    EcPath.Sp.elements lems in
  List.fold_left
  (fun acc db -> acc @ lemmas_of_rw_dbs db)
  [] dbs

let def_rw_lems env = lemmas_of_rewriting_dbs env  default_rewriting_dbs
(*rewriting dbs end*)
    
let testEvalCond (json_hyps : string) (concl_str : string) : unit =
  let hyps, concl = p_t_goal json_hyps concl_str in
  let env = EcEnv.LDecl.toenv hyps in
  let rw_lems = def_rw_lems env in
  printEvalResult (UcEcFormEval.eval_condition hyps concl dft_pi rw_lems)
  
let testSymplify (json_hyps : string) (concl_str : string) : unit =
  let hyps, concl = p_t_goal json_hyps concl_str in
  let env = EcEnv.LDecl.toenv hyps in
  let rw_lems = def_rw_lems env in
  printFormula env (UcEcFormEval.simplify_formula hyps concl rw_lems)
  
let testDeconstructData (json_hyps : string) (concl_str : string) : unit =
  let hyps, concl = p_t_goal json_hyps concl_str in
  let env = EcEnv.LDecl.toenv hyps in
  let rw_lems = def_rw_lems env in
  let tcons , decfs = UcEcFormEval.deconstruct_data hyps concl dft_pi rw_lems in
  print_endline tcons;
  List.iter (fun decf -> printFormula env decf) decfs

let json1 = {|
  [
    {"i" : "int"}
  ]
|}

let json2 = {|
  [
    {"i" : "int"},
    "i=0"
  ]
|}

let json3 = {|
  [
    {"i" : "int"},
    "i=1"
  ]
|}

let () : unit =
  UcState.set_debugging ();
  let common_dir = UcConfig.uc_prelude_dir^"/../../common" in
  let keys_dir = UcConfig.uc_prelude_dir^"/../examples/smc2-ping-adv" in
  UcState.set_include_dirs [common_dir; keys_dir];
  UcEcInterface.init ();
  UcEcInterface.require (UcUtils.dummyloc "AllCore") (Some `Import);
  UcEcInterface.require (UcUtils.dummyloc "test1_of_UcEcFormEval") (Some `Import);
  UcEcInterface.require (UcUtils.dummyloc "UCCore") (Some `Import);
  UcEcInterface.require (UcUtils.dummyloc "KeysExponentsAndPlaintexts") (Some `Export);
  
(*
  testEvalCond json1 "i=0";
  testEvalCond json2 "i=0";
  testEvalCond json3 "i=0";
  
  testSymplify json1 "i=0";
  testSymplify json2 "i=0";
  testSymplify json3 "i=0";
  
  let json={|
    [
      {"x":"int"},
      {"y":"int"},
      {"z":"int"},
      "z = x * 2",
      "x = y + 1"
    ]
  |} in
  let concl = "z" in
  testSymplify json concl;
  
  let json={|
    [
      {"x":"int"},
      {"y":"int"},
      {"z":"int"},
      "z = x * 2",
      "y = 3",
      "x = y + 1"
    ]
  |} in
  let concl = "z" in
  testSymplify json concl;

  let json={|
    [
      {"x":"int"},
      {"y":"int"},
      {"z":"int"},
      "x = y + 1",
      "y = 3",
      "z = x * 2"
    ]
  |} in
  let concl = "z" in
  testSymplify json concl;
  
(*lemma l1 (f : int -> bool, x y z : int) :
  x = y + 1 =>
  x * 2 = z =>
  y = 1 =>
  f (x + z * 2).
proof.
move => H1 H2 H3. (* get where we will start when doing simplification *)
(* if we go the crush route *)
move : H1 H2 H3.
move => />.
(* thus we reduced to a goal of the right form, making us
   feel that the argument to f is the simplification of
   what we started out with, but we can also reduce (not using
   crush) to a goal with f applied to something else *)
move : f.
have -> : (forall f, f 10) = false by smt().
have -> : false = (forall f, f 11) by smt().
move => f.
(*
Current goal

Type variables: <none>

x: int
y: int
z: int
f: int -> bool
------------------------------------------------------------------------
f 11
*)
abort.
*)

  let json={|
    [
      {"x":"int"},
      {"y":"int"},
      {"z":"int"},
      "x = y + 1",
      "x * 2 = z",
      "y = 1"
    ]
  |} in
  let concl = "x + z * 2" in
  testSymplify json concl;
 
(*lemma l4 (f : int -> bool, x1 x2 x3 y1 y2 y3 : int) :
  x1 = y1 /\ x2 = y2 /\ x3 = y3 =>
  x1 = 3 /\ y2 = 4 /\ x3 = 4 =>
  f (x1 + y2 + y3).
proof.
move => H1 H2.
(* starting point *)
move : H1 H2.
move => [#] /=.  (* break up conjunctions *)
move => -> /=.
move => <- /=.  (* -> fails *)
move => -> /=.
move => [#] /=.
move => -> /=.
move => -> /=.
move => -> /=.
abort.
*)  
  let json={|
    [
      {"x1":"int"},
      {"x2":"int"},
      {"x3":"int"},
      {"y1":"int"},
      {"y2":"int"},
      {"y3":"int"},
      "x1 = y1 /\\ x2 = y2 /\\ x3 = y3",
      "x1 = 3 /\\ y2 = 4 /\\ x3 = 4"
    ]
  |} in
  let concl = "x1 + y2 + y3" in
  testSymplify json concl;

(*lemma l5 (f : int -> bool, x1 x2 x3 y1 y2 y3 : int) :
  (x1, x2, x3) = (y1, y2, y3) =>
  x1 = 3 /\ y2 = 4 /\ x3 = 4 =>
  f (x1 + y2 + y3).
proof.
move => H1 H2.
(* starting point *)
move : H1 H2.
move => [#] /=.  (* break up equality of tuples *)
move => -> /=.
move => <- /=.
move => -> /=.
move => [#].
move => -> /=.
move => -> /=.
move => -> /=.
abort.
*)
  let json={|
    [
      {"x1":"int"},
      {"x2":"int"},
      {"x3":"int"},
      {"y1":"int"},
      {"y2":"int"},
      {"y3":"int"},
      "(x1, x2, x3) = (y1, y2, y3)",
      "x1 = 3 /\\ y2 = 4 /\\ x3 = 4"
    ]
  |} in
  let concl = "x1 + y2 + y3" in
  testSymplify json concl;

(*lemma l6 (f : int -> bool, x1 x2 x3 y1 y2 y3 w1 w2 z1 z2 : int) :
  (x1, x2, x3) = (y1, y2, y3) /\ (w1, z1) = (w2, z2) =>
  x1 = 3 /\ y2 = 4 /\ x3 = 4 /\ z2 = 6 /\ w1 = 12 =>
  f (x1 + y2 + y3 + z2 + w1).
proof.
move => H1 H2.
(* starting point *)
move : H1 H2.
move => [#].  (* break up conjuctions and equality of tuples *)
move => -> /=.
move => <- /=.
move => -> /=.
move => -> /=.
move => <- /=.
move => [#].
move => -> /=.
move => -> /=.
move => -> /=.
move => -> /=.
move => -> /=.
abort.*)
  let json={|
    [
      {"x1":"int"},
      {"x2":"int"},
      {"x3":"int"},
      {"y1":"int"},
      {"y2":"int"},
      {"y3":"int"},
      {"w1":"int"},
      {"w2":"int"},
      {"z1":"int"},
      {"z2":"int"},
      "(x1, x2, x3) = (y1, y2, y3) /\\ (w1, z1) = (w2, z2)",
      "x1 = 3 /\\ y2 = 4 /\\ x3 = 4 /\\ z2 = 6 /\\ w1 = 12"
    ]
  |} in
  let concl = "x1 + y2 + y3 + z2 + w1" in
  testSymplify json concl;
  
(*lemma l7 (f : int -> bool, x1 x2 x3 y1 y2 y3 : int, a b : int * int * int) :
  (x1, x2, x3) = a =>
  (y1, y2, y3) = b =>
  a = b =>
  x1 = 1 /\ x2 = 2 /\ y3 = 3 =>
  f (x1 + x2 + x3 + y1 + y2 + y3).
proof.
move => H1 H2 H3.
(* starting point *)
move : H1 H2 H3.
move => <- /=.
move => <- /=.
move => [#].
move => -> /=.
move => -> /=.
move => -> /=.
move => [#].
move => -> /=.
move => -> /=.
move => -> /=.
abort.
*)
  let json={|
    [
      {"x1":"int"},
      {"x2":"int"},
      {"x3":"int"},
      {"y1":"int"},
      {"y2":"int"},
      {"y3":"int"},
      {"a":"int * int * int"},
      {"b":"int * int * int"},
      "(x1, x2, x3) = a",
      "(y1, y2, y3) = b",
      "a = b",
      "x1 = 1 /\\ x2 = 2 /\\ y3 = 3"
    ]
  |} in
  let concl = "x1 + x2 + x3 + y1 + y2 + y3" in
  testSymplify json concl;(*TODO - check*)

(*lemma l8 (f : int -> bool, x1 x2 x3 y1 y2 y3 : int, a b : int * int * int) :
  b = (y1, y2, y3) =>
  (x1, x2, x3) = a =>
  a = b =>
  x1 = 1 /\ x2 = 2 /\ y3 = 3 =>
  f (x1 + x2 + x3 + y1 + y2 + y3).
proof.
move => H1 H2 H3.
(* starting point *)
move : H1 H2 H3.
move => -> /=.
move => <- /=.
move => [#].
move => -> /=.
move => -> /=.
move => -> /=.
move => [#].
move => -> /=.
move => -> /=.
move => -> /=.
abort.
*)
  let json={|
    [
      {"x1":"int"},
      {"x2":"int"},
      {"x3":"int"},
      {"y1":"int"},
      {"y2":"int"},
      {"y3":"int"},
      {"a":"int * int * int"},
      {"b":"int * int * int"},
      "b = (y1, y2, y3)",
      "(x1, x2, x3) = a",
      "a = b",
      "x1 = 1 /\\ x2 = 2 /\\ y3 = 3"
    ]
  |} in
  let concl = "x1 + x2 + x3 + y1 + y2 + y3" in
  testSymplify json concl;


(*lemma l9 (f : int -> bool, x1 x2 x3 y1 y2 y3 : int, a b : int * int * int) :
  a = b =>
  b = (y1, y2, y3) =>
  (x1, x2, x3) = a =>
  x1 = 1 /\ x2 = 2 /\ y3 = 3 =>
  f (x1 + x2 + x3 + y1 + y2 + y3).
proof.
move => H1 H2 H3.
(* starting point *)
move : H1 H2 H3.
move => -> /=.
move => -> /=.
move => [#].
move => -> /=.
move => -> /=.
move => -> /=.
move => [#].
move => -> /=.
move => -> /=.
move => -> /=.
abort.*)  
  let json={|
    [
      {"x1":"int"},
      {"x2":"int"},
      {"x3":"int"},
      {"y1":"int"},
      {"y2":"int"},
      {"y3":"int"},
      {"a":"int * int * int"},
      {"b":"int * int * int"},
      "a = b",
      "b = (y1, y2, y3)",
      "(x1, x2, x3) = a",
      "x1 = 1 /\\ x2 = 2 /\\ y3 = 3"
    ]
  |} in
  let concl = "x1 + x2 + x3 + y1 + y2 + y3" in
  testSymplify json concl;
  
(*  
lemma l3 (f : int -> bool, p : int -> bool, x y z : int) :
  x = y + 1 =>
  p (x + y) =>
  x * 2 = z =>
  y = 1 =>
  f (if p (2 * y + 1)
     then x + z * 2
     else 14).
proof.
move => H1 H2 H3 H4 /=.
(* starting point *)
move : H1 H2 H3 H4.
move => -> /=.
(* when we have assumptions that are not either equalities or
   conjunctions (see below for how we handle the latter), we
   move them to the end so that rewritings can happen in them *)
move => H1 H2 H3 /=.
move : H2 H3 H1.  (* push p (y + 1 + y) to end *)
move => <- /=.
move => -> /=.
move => -> /=.
abort.
*)

  let json={|
    [
      {"x":"int"},
      {"y":"int"},
      {"z":"int"},
      {"p":"int -> bool"},
      "x = y + 1",
      "p (x + y)",
      "x * 2 = z",
      "y = 1"
    ]
  |} in
  let concl = "if p (2 * y + 1)
     then x + z * 2
     else 14" in
  testSymplify json concl;
  
(*
lemma l10 (f : int -> bool, p : int -> bool, x y z : int) :
  (if p (x + y) \/ p (y * 2) then z = 1 else z = 2) =>
  p (x + y) =>
  x = y + 1 =>
  y = 12 =>
  f z.
proof.
move => H1 H2 H3 H4.
(* starting point *)
move : H1 H2 H3 H4.
move => H1 H2 H3 H4 /=.
move : H3 H4 H1 H2.
move => -> /=.
move => -> /=.
move => H1 H2.
move : H2 H1.
move => -> /=.
move => -> /=.
abort.
*)

  let json={|
    [
      {"x":"int"},
      {"y":"int"},
      {"z":"int"},
      {"p":"int -> bool"},
      "(if p (x + y) \\/ p (y * 2) then z = 1 else z = 2)",
      "p (x + y)",
      "x = y + 1",
      "y = 12"
    ]
  |} in
  let concl = "z" in
  testSymplify json concl;
  
  let json={|
    [
    ]
  |} in
  let concl = "A 7" in
  testDeconstructData json concl;

let json={|
    [
    ]
  |} in
  let concl = "F 7 true" in
  testDeconstructData json concl;
  
let json={|
    [
    ]
  |} in
  let concl = "T (7 , true)" in
  testDeconstructData json concl;

let json={|
    [
    ]
  |} in
  let concl = "U" in
  testDeconstructData json concl;
  *)
(*
lemma n28
(
func: addr,
adv: addr,
pt1: port,
pt2: port,
zmdfdb: bool -> bool
) :
envport func adv pt2 =>
envport func adv pt1 =>
inc func adv =>
([1; 1; 1] <= func \/ ([1; 1; 1] <= [1; 1] /\ ! adv <= func ++ [1; 1])).
proof.
move => H1 H2 H3.
(* we would like this to simplify to:
[1; 1; 1] <= func
*)
rewrite envport_ext_func_iff_helper //.
(*
[1; 1; 1] <= func \/ [1; 1; 1] <= [1; 1] /\ !false
*)
move => />.  (* because second disjunct is false (not true), doesn't recognize *)
(*
[1; 1; 1] <= func \/ [1; 1; 1] <= [1; 1]
*)
delta.
(* this is why selective delta is important - we'd like to only
   apply delta when all args to operator are made entirely out of
   constructors *)
(*
(let r = lpo [1; 1; 1] func in r = LT \/ r = Eq) \/
let r = lpo [1; 1; 1] [1; 1] in r = LT \/ r = Eq
*)
simplify.
(*
(if func = [] then GT
 else
   if 1 = head 1 func then
     if behead func = [] then GT
     else
       if 1 = head 1 (behead func) then
         if behead (behead func) = [] then GT
         else
           if 1 = head 1 (behead (behead func)) then
             if behead (behead (behead func)) = [] then Eq else LT
           else Inc
       else Inc
   else Inc) =
LT \/
(if func = [] then GT
 else
   if 1 = head 1 func then
     if behead func = [] then GT
     else
       if 1 = head 1 (behead func) then
         if behead (behead func) = [] then GT
         else
           if 1 = head 1 (behead (behead func)) then
             if behead (behead (behead func)) = [] then Eq else LT
           else Inc
       else Inc
   else Inc) =
Eq
*)


  let json={|
    [
      {"func":"addr"},
      {"adv":"addr"},
      {"pt1":"port"},
      {"pt2":"port"},
      "envport func adv pt2",
      "envport func adv pt1",
      "inc func adv"
    ]
  |} in
  let concl = "[1; 1; 1] <= func \\/ ([1; 1; 1] <= [1; 1] /\\ ! adv <= func ++ [1; 1])" in
  testSymplify json concl;


(*
func: addr
adv: addr
text1: text
text2: text
pt1: port
pt2: port
rand: exp
rand1: exp
nissef: text option -> bool
ffujff: rand1 \in dexp
htwjff: rand \in dexp
nfzjff: envport func adv pt2
zpbkff: envport func adv pt1
tydkff: inc func adv
------------------------------------------------------------------------
nissef (epdp_text_key.`dec
  (epdp_text_key.`enc text1 ^^ (g ^ rand1 ^ rand) ^^ kinv (g ^ rand ^ rand1)))
 *)

  let json={|
    [
      {"func":"addr"},
      {"adv":"addr"},
      {"text1":"text"},
      {"text2":"text"},
      {"pt1":"port"},
      {"pt2":"port"},
      {"rand":"exp"},
      {"rand1":"exp"},
      "rand1 \\in dexp",
      "rand \\in dexp",
      "envport func adv pt2",
      "envport func adv pt1",
      "inc func adv"
    ]
  |} in
  let concl = "epdp_text_key.`dec
  (epdp_text_key.`enc text1 ^^ (g ^ rand1 ^ rand) ^^ kinv (g ^ rand ^ rand1))" in
  testSymplify json concl;

  testDeconstructData json concl;
*)  
(*
func: addr
adv: addr
IncFuncAdv: inc func adv
text1: text
text2: text
pt1: port
pt2: port
envport_pt1: envport func adv pt1
envport_pt2: envport func adv pt2
rand: exp
Hrand: rand \in dexp
iufue: (port -> bool) -> bool
------------------------------------------------------------------------
iufue (envport (func ++ [1; 1; 1]) adv)

 *)

  let json={|
    [
      {"func":"addr"},
      {"adv":"addr"},
      {"text1":"text"},
      {"text2":"text"},
      {"pt1":"port"},
      {"pt2":"port"},
      {"rand":"exp"},
      "rand \\in dexp",
      "envport func adv pt2",
      "envport func adv pt1",
      "inc func adv"
    ]
  |} in
  let concl = "envport (func ++ [1; 1; 1]) adv (func ++ [1; 1], 2)" in
  testSymplify json concl;

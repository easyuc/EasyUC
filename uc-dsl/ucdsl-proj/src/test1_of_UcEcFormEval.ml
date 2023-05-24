open UcEcHypothesisSerialization
open UcEcFormEval

let printEvalResult (res : UcEcFormEval.evalConditionResult) : unit =
  match res with
  | Bool true  -> print_endline "TRUE"
  | Bool false -> print_endline "FALSE"
  | Undecided  -> print_endline "UNDECIDED"
  
let printFormula env (form : EcCoreFol.form) : unit =
  Format.eprintf "%a@."
    (EcPrinting.pp_form (EcPrinting.PPEnv.ofenv env)) 
    (form)

(*copied from UcEcHypothesisSerialization*)
let parse_trans_frm (env : EcEnv.env) (frm_str : string) : EcCoreFol.form =
  let reader = EcIo.from_string_pformula frm_str in
  let pformula = EcIo.parse_pformula reader in
  let ue  = EcTyping.transtyvars env (EcLocation._dummy, None) in
  EcTyping.trans_form_opt env ue pformula None

let p_t_concl (hyps : EcEnv.LDecl.hyps) (concl : string) : EcCoreFol.form =
  let env = EcEnv.LDecl.toenv hyps in
  parse_trans_frm env concl
  
let p_t_goal (json_hyps : string) (concl_str : string) : EcEnv.LDecl.hyps * EcCoreFol.form =
  let hyps = json_hyps2ldecl_hyps json_hyps in
  let concl = p_t_concl hyps concl_str in
  hyps, concl
    
let testEvalCond (json_hyps : string) (concl_str : string) : unit =
  let hyps, concl = p_t_goal json_hyps concl_str in
  printEvalResult (UcEcFormEval.evalCondition hyps concl)
  
let testSymplify (json_hyps : string) (concl_str : string) : unit =
  let hyps, concl = p_t_goal json_hyps concl_str in
  let env = EcEnv.LDecl.toenv hyps in
  printFormula env (UcEcFormEval.simplifyFormula hyps concl)
  
let testDeconstructData (json_hyps : string) (concl_str : string) : unit =
  let hyps, concl = p_t_goal json_hyps concl_str in
  let env = EcEnv.LDecl.toenv hyps in
  printFormula env (UcEcFormEval.deconstructData hyps concl)
  

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
  UcEcInterface.init ();
  UcEcInterface.require (UcUtils.dummyloc "AllCore") (Some `Import);
  UcEcInterface.require (UcUtils.dummyloc "test1_of_UcEcFormEval") (Some `Import);

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
  
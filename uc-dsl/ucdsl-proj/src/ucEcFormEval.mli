type eval_condition_result = 
  | Bool of bool
  | Undecided

(*
  hyps must be ordered so that a formula references only previous formulas/variables
  formulas cannot use types with Tunivar nodes - have to be unified
  the conclusion form must be a predicate (return bool)
*)  
val eval_condition : EcEnv.LDecl.hyps -> 
                     EcCoreFol.form ->
                     EcProvers.prover_infos -> 
                     EcPath.path list ->  (* rw lemmas *)
                     eval_condition_result

val simplify_formula : EcEnv.LDecl.hyps ->
                       EcCoreFol.form ->
                       EcPath.path list ->  (* rw lemmas *)
                       EcCoreFol.form

val deconstruct_data : EcEnv.LDecl.hyps -> 
                       EcCoreFol.form ->
                       EcProvers.prover_infos ->
                       EcPath.path list ->  (* rw lemmas *)
                       EcSymbols.symbol * (EcCoreFol.form list)

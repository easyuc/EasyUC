type evalConditionResult = 
  | Bool of bool
  | Undecided

(*
  hyps must be ordered so that a formula references only previous formulas/variables
  formulas cannot use types with Tunivar nodes - have to be unified
  the conclusion form must be a predicate (return bool)
*)  
val evalCondition  : EcBaseLogic.hyps -> EcCoreFol.form -> evalConditionResult

val simplifyFormula :  EcBaseLogic.hyps -> EcCoreFol.form -> EcCoreFol.form

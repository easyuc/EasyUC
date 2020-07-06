(* ucExpressions.mli *)

open UcTypes
open UcSpec

val checkExpression: (qid -> typ) -> expressionL -> typ
val isDistribution: typ -> bool
val getDistrubutionTyp: typ -> typ

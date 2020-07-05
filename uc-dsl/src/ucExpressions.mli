(* ucExpressions.mli *)

open UcParseTree
open UcTypes

val checkExpression: (qid->typ)->expressionL->typ
val isDistribution: typ->bool
val getDistrubutionTyp: typ->typ

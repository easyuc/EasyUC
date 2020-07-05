open UcParseTree
open UcTypechecked
open UcTypes

val checkExpression: (qid->typ)->expressionL->typ
val isDistribution: typ->bool
val getDistrubutionTyp: typ->typ

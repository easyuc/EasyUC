open DlParseTree
open DlParsedTree
open DlTypes

val checkExpression: (qid->typ)->expressionL->typ
val isDistribution: typ->bool
val getDistrubutionTyp: typ->typ

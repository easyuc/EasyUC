uc_requires X.
uc_clone X as X1.
uc_clone X as X2.

direct A {
in x@bla()
}

direct D {D:A}

functionality R(F1:X1.D,F2:X2.D) implements D {
 party P serves D.D {initial state I {match message with * => {fail.}end}}
}

uc_requires Req.

direct A {
in x@bla()
}

direct D {D:A}

functionality R(F1:Req.D,F2:D) implements D {
 party P serves D.D {initial state I {match message with * => {fail.}end}}
}

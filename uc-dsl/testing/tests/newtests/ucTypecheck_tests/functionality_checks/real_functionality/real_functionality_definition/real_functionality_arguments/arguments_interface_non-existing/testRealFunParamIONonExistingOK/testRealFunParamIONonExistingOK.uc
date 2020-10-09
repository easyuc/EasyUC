direct A {
in x@bla()
}

direct D {d:A}

functionality R(F1:D,F2:D) implements D {
 party P serves D.d {initial state I {match message with * => {fail.}end}}
}

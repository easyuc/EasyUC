direct A {
in x@bla()
}

direct D {D:A}

functionality R(F1:D,F2:C) implements D {
 party P serves D.D {initial state I {match message with * => {fail.}end}}
}

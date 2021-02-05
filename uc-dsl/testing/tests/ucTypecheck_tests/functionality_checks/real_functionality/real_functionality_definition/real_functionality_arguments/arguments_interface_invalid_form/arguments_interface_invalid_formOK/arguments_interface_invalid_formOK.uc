direct A {
in x@bla()
}

direct D {D:A}

functionality R(F1:D) implements D {
 party P serves D.D {initial state I {match message with * => {fail.}end}}
}

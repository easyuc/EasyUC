direct A {
in x@bla()
}

direct D {d:A}

functionality R(F1:D,F2:C) implements D {
 party P serves d {initial state I {match message with othermsg => {fail.}end}}
}

direct D {
in x@bla()
}

direct A {d:D}

adversarial C {
in bla()
}

adversarial B {c:C}

functionality R() implements A B {
 party P serves d,c {initial state I {match message with othermsg => {fail.}end}}
}

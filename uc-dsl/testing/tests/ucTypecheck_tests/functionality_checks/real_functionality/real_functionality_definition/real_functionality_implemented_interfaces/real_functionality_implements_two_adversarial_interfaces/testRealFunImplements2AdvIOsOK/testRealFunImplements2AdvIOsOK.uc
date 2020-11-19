direct D {
in x@bla()
}

direct A {D:D}

adversarial C {
in bla()
}

adversarial B {C:C}

functionality R() implements A B {
 party P serves A.D B.C {initial state I {match message with * => {fail.}end}}
}

adversarial D {
in bla()
}

adversarial A {d:D}

adversarial C {
in bla()
}

adversarial B {c:C}

functionality R() implements A B {
 party P serves A.d B.c {initial state I {match message with * => {fail.}end}}
}

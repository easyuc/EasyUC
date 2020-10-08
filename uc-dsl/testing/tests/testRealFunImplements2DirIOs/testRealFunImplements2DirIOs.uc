direct D {
in x@bla()
}

direct A {d:D}

direct C {
in x@bli()
}

direct B {c:C}

functionality R() implements A B {
 party P serves A.d B.c {initial state I {match message with * => {fail.} end }}
}

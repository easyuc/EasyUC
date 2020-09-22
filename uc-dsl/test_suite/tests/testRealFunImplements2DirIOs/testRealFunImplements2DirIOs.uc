direct D {
in x@bla()
}

direct A {d:D}

direct C {
in x@bli()
}

direct B {c:C}

functionality R() implements A B {
 party P serves d,c {initial state I {match message with othermsg => {fail.} end }}
}

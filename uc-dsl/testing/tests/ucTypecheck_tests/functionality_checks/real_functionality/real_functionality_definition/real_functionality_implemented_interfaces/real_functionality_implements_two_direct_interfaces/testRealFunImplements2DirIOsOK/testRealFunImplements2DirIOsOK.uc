direct D {
in x@bla()
}

direct A {d:D}

direct C {
in x@bli()
}

direct B {c:C}

functionality R() implements A  {
 party P serves A.d {initial state I {match message with * => {fail.} end }}
}

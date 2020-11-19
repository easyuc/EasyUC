direct D {
in x@bla()
}

direct A {D:D}

direct C {
in x@bli()
}

direct B {C:C}

functionality R() implements A  {
 party P serves A.D {initial state I {match message with * => {fail.} end }}
}

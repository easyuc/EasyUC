direct D {
in x@bla()
}

direct A {D:D}

functionality R() implements D {
 party P serves D {initial state I {match message with * => {fail.} end }}
}

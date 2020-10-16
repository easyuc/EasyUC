direct A {
in x@bla()
}

direct D {a:A}

functionality F(F1:D,F2:D) implements D {
 party P serves D.a {
  initial state I {match message with * => {fail.} end}
 }
}

direct A {
in x@bla()
}

direct D {A:A}

functionality F(F1:D,F2:D) implements D {
 party P serves D.A {
  initial state I {match message with * => {fail.} end}
 }
}

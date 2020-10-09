direct A {
in x@bla()
}

direct D {a:A}

functionality A(F1:D,F2:D) implements D {
 party P serves A.a {
  initial state I {match message with * => {fail.} end}
 }
}

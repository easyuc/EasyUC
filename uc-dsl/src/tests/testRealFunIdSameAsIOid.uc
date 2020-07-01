direct A {
in x@bla()
}

direct D {a:A}

functionality A(F1:D,F2:D) implements D {
 party P serves a {
  initial state I {match message with othermsg => {fail.} end}
 }
}

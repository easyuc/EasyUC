direct A {
in x@bla()
}

direct D {A1:A A2:A}

functionality F implements D {
 party P1 serves D.A1 {
  initial state I {match message with * => {fail.} end}
 }
 party P2 serves D.A2 {
  initial state I {match message with * => {fail.} end}
 }
}

direct A {
in x@bla()
}

direct D {A1:A A2:A}

functionality F implements D {
 party P serves D.A1 {
  initial state I {match message with * => {fail.} end}
 }
 party P serves D.A2 {
  initial state I {match message with * => {fail.} end}
 }
}

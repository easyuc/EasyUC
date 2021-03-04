direct D' {
in  x@bla()
out bli()@x
}

direct D {D:D'}

functionality F(G:D) implements D {

 party P serves D.D {

  initial state I {
   match message with
     x@D.D.bla() => {send G.D.bla() and transition I.}
   | * => {fail.}
   end
  }
 }
}

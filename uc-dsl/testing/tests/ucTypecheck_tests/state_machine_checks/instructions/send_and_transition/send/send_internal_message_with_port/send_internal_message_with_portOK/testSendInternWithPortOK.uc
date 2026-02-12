uc_requires X.

uc_clone X.

direct D' {
in  x@bla()
out bli()@x
}

direct D {D:D'}

functionality F(G:X.D) implements D {

 party P serves D.D {

  initial state I {
   match message with
     x@D.D.bla() => {send G.D.bla() and transition J.}
   | * => {fail.}
   end
  }

  state J { match message with * => { fail. } end }
 }
}

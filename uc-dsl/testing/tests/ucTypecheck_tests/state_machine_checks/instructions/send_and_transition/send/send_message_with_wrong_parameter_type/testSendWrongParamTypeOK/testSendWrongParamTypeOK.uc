ec_requires +KeysExponentsAndPlainTexts.

direct D' {
in  x@bla(k:key)
out bli()@x
}

direct D {D:D'}

functionality F(G:D) implements D {

 party P serves D.D {

  initial state I {
   match message with
     x@D.D.bla(k) => {send G.D.bla(g) and transition J.}
   | * => {fail.}
   end
  }

  state J { match message with * => { fail. } end }
 }
}

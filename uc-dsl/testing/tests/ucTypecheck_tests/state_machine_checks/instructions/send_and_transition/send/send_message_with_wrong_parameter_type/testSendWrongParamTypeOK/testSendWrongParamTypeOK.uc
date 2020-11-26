ec_requires KeysExponentsAndPlainTexts.

direct D_ {
in  x@bla(k:key)
out bli()@x
}

direct D {D:D_}

functionality F(G:D) implements D {

 party P serves D.D {

  initial state I {
   match message with
     D.D.* => {send G.D.bla(g) and transition I.}
   | * => {fail.}
   end
  }
 }
}

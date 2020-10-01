ec_requires KeysExponentsAndPlainTexts.

direct d {
in  x@bla(k:key)
out bli()@x
}

direct D {D:d}

functionality F(G:D) implements D {

 party P serves D.D {

  initial state I {
   match message with
     sender@D.D.bla(k) => {send G.D.bla(sender) and transition I.}
   | * => {fail.}
   end
  }
 }
}

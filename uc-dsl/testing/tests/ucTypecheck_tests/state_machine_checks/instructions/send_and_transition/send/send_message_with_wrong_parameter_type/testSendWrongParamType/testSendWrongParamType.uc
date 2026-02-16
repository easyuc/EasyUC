uc_requires X.
ec_requires +KeysExponentsAndPlainTexts.

uc_clone X.

direct D' {
in  x@bla(k:key)
out bli()@x
}

direct D {D:D'}

functionality F(G:X.D) implements D {

 party P serves D.D {

  initial state I {
   match message with
     sender@D.D.bla(k) => {send G.D.bla(sender) and transition J.}
   | * => {fail.}
   end
  }

  state J { match message with * => { fail. } end }
 }
}

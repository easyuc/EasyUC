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
   var k:key;
   match message with
     sender@D.D.bla(k1) => {if (g=g) {k<-g;} else {k<-g;} send G.D.bla(k) and transition J.}
   | * => {fail.}
   end
  }

  state J { match message with * => { fail. } end }
 }
}

ec_requires KeysExponentsAndPlainTexts.

direct d {
in  x@bla(k:key)
out bli()@x
}

direct D {D:d}

functionality F(G:D) implements D {

 party P serves D.D {

  initial state I {
   var k:key;
   match message with
     sender@D.D.bla(k1) => {if (g=g) {k<-g;} send G.D.bla(k) and transition I.}
   | * => {fail.}
   end
  }
 }
}

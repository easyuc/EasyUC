ec_requires +KeysExponentsAndPlainTexts.

direct D' {
in  x@bla(k:key)
out bli()@x
}

direct D {D:D'}

functionality F(G:D) implements D {

 party P serves D.D {

  initial state I {
   var k:key;
   match message with
     sender@D.D.bla(k1) => {send D.D.bli()@sender and transition I. k<-g;}
   | * => {fail.}
   end
  }
 }
}

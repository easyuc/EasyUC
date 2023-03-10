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
     sender@D.D.bla(k1) => {send D.D.bli()@sender and transition J. k<-g;}
   | * => {fail.}
   end
  }

  state J { match message with * => { fail. } end }
 }
}

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
     y@D.D.bla(k') => {fail. k<-g;}
   | * => {fail.}
   end
  }
 }
}

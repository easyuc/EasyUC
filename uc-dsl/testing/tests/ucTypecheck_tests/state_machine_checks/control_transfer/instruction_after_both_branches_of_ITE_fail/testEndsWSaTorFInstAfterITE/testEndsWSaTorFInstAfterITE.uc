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
     y@D.D.bla(k') => {if (g=g) {fail.} else {fail.} k<-g;}
   | * => {fail.}
   end
  }
 }
}

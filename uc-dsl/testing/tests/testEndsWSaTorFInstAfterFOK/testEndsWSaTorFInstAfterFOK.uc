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
     D.D.* => {fail.}
   | * => {fail.}
   end
  }
 }
}

ec_requires KeysExponentsAndPlainTexts.

direct D_ {
in  x@bla(k:key)
out bli()@x
}

direct D {D:D_}
functionality F(G:D) implements D {

 party P serves D.D {

  initial state I {
   var k:key;
   match message with
     D.D.* => {if (g=g) {fail.} else {fail.}}
   | * => {fail.}
   end
  }
 }
}

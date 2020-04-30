requires KeysExponentsAndPlainTexts.

direct d {
in  x@bla(k:key)
out bli()@x
}

direct D {D:d}

functionality F(G:D) implements D {

 party P serves D {

  initial state I {
   var k:key;
   match message with
     sender@D.othermsg => {if (g=g) {k<-g;} else {k<-g;} send G.D.bla(k) and transition I.}
   | othermsg => {fail.}
   end
  }
 }
}

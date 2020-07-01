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
     sender@D.othermsg => {k<-g;}
   | othermsg => {fail.}
   end
  }
 }
}

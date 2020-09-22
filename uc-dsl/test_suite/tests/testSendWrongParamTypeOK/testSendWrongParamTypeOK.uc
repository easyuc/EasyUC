requires KeysExponentsAndPlainTexts.

direct d {
in  x@bla(k:key)
out bli()@x
}

direct D {D:d}

functionality F(G:D) implements D {

 party P serves D {

  initial state I {
   match message with
     sender@D.othermsg => {send G.D.bla(g) and transition I.}
   | othermsg => {fail.}
   end
  }
 }
}

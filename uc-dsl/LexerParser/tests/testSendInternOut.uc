requires KeysExponentsAndPlainTexts.

direct d {
in  x@bla()
out bli()@x
}

direct D {D:d}

functionality F(G:D) implements D {

 party P serves D {

  initial state I {
   match message with
     sender@D.othermsg => {send G.D.bli() and transition I.}
   | othermsg => {fail.}
   end
  }
 }
}

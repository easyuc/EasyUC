direct d {
in  x@bla()
out bli()@x
}

direct D {D:d}

functionality F(G:D) implements D {

 party P serves D {

  initial state I {
   match message with
     sender@D.othermsg => {if (sender=sender) {send G.D.bla() and transition I.} else {fail.}}
   | othermsg => {fail.}
   end
  }
 }
}

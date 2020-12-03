direct D_ {
in  x@bla()
out bli()@x
}

direct D {D:D_}

functionality F(G:D) implements D {

 party P serves D.D {

  initial state I {
   match message with
     sender@D.D.bla() => {send G.D.bla(sender) and transition I.}
   | * => {fail.}
   end
  }
 }
}

direct D_ {
in  x@bla()
out bli()@x
}

direct D {D:D_}

functionality F(G:D) implements D {

 party P serves D.D {

  initial state I {
   match message with
     D.D.* => {send G.D.bli() and transition I.}
   | * => {fail.}
   end
  }
 }
}

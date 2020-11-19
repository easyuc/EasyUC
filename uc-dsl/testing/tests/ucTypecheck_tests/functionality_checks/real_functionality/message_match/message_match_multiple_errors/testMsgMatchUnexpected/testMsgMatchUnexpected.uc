direct D_ {
in x@bla()
in x@blb()
out bli()@x
out blj()@x
}

direct D {D:D_}

adversarial A_ {
in  bla()
in  blb()
out bli()
}

adversarial A {A:A_}

functionality F() implements D A_{

  initial state Is 
  {
   match message with
    *  => {fail.}
   end
  }
}

functionality S(X:D) implements D A {

 subfun F=F

 party P serves D.D A.A {
  initial state Is 
  {
   match message with
     p@D.D.bla => {fail.}
   | D.D.* => {fail.}
   | X.D.bli => {fail.}
   | X.D.* => {fail.}
   | F.D.bla => {fail.}
   | F.* => {fail.}
   | A.bla => {fail.}
   | A.* => {fail.}
   end
  }
 }
}


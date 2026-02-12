uc_requires X.
uc_clone X as X1.
uc_clone X as X2.

direct D' {
in x@bla()
in x@blb()
out bli()@x
out blj()@x
}

direct D {D:D'}

adversarial A' {
in  bla()
in  blb()
out bli()
}

adversarial A {A:A'}

functionality S(X:X2.D) implements D A {

 subfun F=X1.F

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


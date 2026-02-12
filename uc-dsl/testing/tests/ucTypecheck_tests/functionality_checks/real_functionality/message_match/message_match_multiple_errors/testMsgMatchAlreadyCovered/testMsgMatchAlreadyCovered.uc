uc_requires X.
uc_clone X as X1.
uc_clone X as X2.

direct D' {
in x@bla()
out bli()@x
}

direct D {D:D'}

adversarial A' {
in  bla()
out bli()
}

adversarial A {A:A'}

functionality S(X:X2.D) implements D A {
 subfun F=X1.F

 party P serves D.D A.A {
  initial state Is 
  {
   match message with
     sender@D.D.bla => {fail.}
   | D.D.* => {fail.}
   | X.D.bli => {fail.}
   | F.D.bli => {fail.}
   end
  }
 }
}


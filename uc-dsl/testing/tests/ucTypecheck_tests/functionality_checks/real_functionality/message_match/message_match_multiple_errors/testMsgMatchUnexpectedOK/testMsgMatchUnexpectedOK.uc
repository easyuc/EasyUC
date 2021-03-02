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

functionality F() implements D A'{

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
   | X.D.*  => {fail.}
   | F.D.bli => {fail.}
   | F.D.* => {fail.}
   | A.A.bla => {fail.}
   | A.A.* => {fail.}
   end
  }
 }
}


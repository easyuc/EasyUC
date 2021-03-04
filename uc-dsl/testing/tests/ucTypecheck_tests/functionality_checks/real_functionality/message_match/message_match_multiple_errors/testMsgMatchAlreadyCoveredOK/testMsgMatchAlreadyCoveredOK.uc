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

functionality F() implements D A'{

  initial state Is 
  {
   match message with
    * => {fail.}
   end
  }
}

functionality S(X:D) implements D A {

 subfun F=F

 party P serves D.D A.A {
  initial state Is 
  {
   match message with
     sender@D.D.bla => {fail.}
   | X.D.bli => {fail.}
   | F.D.bli => {fail.}
   | A.A.bla => {fail.}
   end
  }
 }
}


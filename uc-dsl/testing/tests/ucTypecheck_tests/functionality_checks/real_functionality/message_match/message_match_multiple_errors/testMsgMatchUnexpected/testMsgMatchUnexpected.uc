direct d {
in x@bla()
in x@blb()
out bli()@x
out blj()@x
}

direct D {D:d}

adversarial a {
in  bla()
in  blb()
out bli()
}

adversarial A {A:a}

functionality F() implements D a{

  initial state Is 
  {
   match message with
    *  => {fail.}
   end
  }
}

functionality S(X:D) implements D A {

 subfun f=F

 party P serves D.D A.A {
  initial state Is 
  {
   match message with
     p@D.D.bla => {fail.}
   | D.D.* => {fail.}
   | X.D.bli => {fail.}
   | X.D.* => {fail.}
   | f.D.bla => {fail.}
   | f.* => {fail.}
   | A.bla => {fail.}
   | A.* => {fail.}
   end
  }
 }
}


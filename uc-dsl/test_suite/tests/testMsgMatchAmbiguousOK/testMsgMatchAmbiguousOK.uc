direct d {
in x@bla()
out bli()@x
}

direct D {D:d}

adversarial a {
in  bla()
out bli()
}

adversarial A {A:a}

functionality F() implements D a{
  initial state Is 
  {
   match message with
    * => {fail.}
   end
  }
}

functionality S(X:D) implements D A {

 subfun f=F

 party P serves D.D A.A {
  initial state Is 
  {
   match message with
     sender@D.D.bla => {fail.}
   | *  => {fail.}
   end
  }
 }
}


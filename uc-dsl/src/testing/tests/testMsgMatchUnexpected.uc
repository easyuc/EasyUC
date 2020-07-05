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

functionality F() implements D {
 party P serves D {
  initial state Is 
  {
   match message with
    othermsg => {fail.}
   end
  }
 }
}

functionality S(X:D) implements D A {

 subfun f=F()

 party P serves D,A {
  initial state Is 
  {
   match message with
     D.bla => {fail.}
   | D.othermsg => {fail.}
   | X.D.bli => {fail.}
   | X.othermsg => {fail.}
   | f.D.bla => {fail.}
   | f.othermsg => {fail.}
   | A.bla => {fail.}
   | A.othermsg => {fail.}
   end
  }
 }
}


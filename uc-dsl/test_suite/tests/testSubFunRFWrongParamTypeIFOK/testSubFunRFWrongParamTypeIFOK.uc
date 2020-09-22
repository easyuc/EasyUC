direct a {
in x@bla()
}

direct A {a:a}

direct d {
in x@bli()
}

direct D {d:d}

adversarial C {
out bla()
}

functionality I() implements D C {

  initial state Is
  {
   match message with
    othermsg => {fail.}
   end
  }
}

functionality S(X:D) implements A {
 party P serves a {
  initial state Isus 
  {
   match message with
    othermsg => {fail.}
   end
  }
 }
}

functionality R() implements A {

 subfun Q=I()
 subfun SF=S(Q)

 party P serves a {
  initial state Isus 
  {
   match message with
    othermsg => {fail.}
   end
  }
 }
}

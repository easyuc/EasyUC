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

functionality I() implements A C {

  initial state Is
  {
   match message with
    * => {fail.}
   end
  }
}

functionality S(X:D) implements A C{
  initial state Isus 
  {
   match message with
    * => {fail.}
   end
  }
}

functionality R() implements A {

 subfun Q=I
 subfun SF=S(Q)

 party P serves A.a {
  initial state Isus 
  {
   match message with
    * => {fail.}
   end
  }
 }
}

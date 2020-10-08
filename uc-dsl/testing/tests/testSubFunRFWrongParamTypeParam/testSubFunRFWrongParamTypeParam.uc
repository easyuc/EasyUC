direct a {
in x@bla()
}

direct A {a:a}

direct d {
in x@bli()
}

adversarial C {
in bla()
}

direct D {d:d}

functionality S implements A C{
  initial state Isus 
  {
   match message with
    * => {fail.}
   end
  }
}

functionality R(Q:A) implements A  {

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

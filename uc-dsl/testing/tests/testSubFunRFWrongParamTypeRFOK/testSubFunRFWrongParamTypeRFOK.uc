direct a {
in x@bla()
}

direct A {a:a}

direct d {
in x@bli()
}

direct D {d:d}

adversarial C {
in bla()
}


functionality E() implements D C {

  initial state Isus 
  {
   match message with
    * => {fail.}
   end
  }
}

functionality S() implements A C {
  initial state Isus 
  {
   match message with
    * => {fail.}
   end
  }

}

functionality R() implements A {

 subfun Q=E
 subfun SF=S

 party P serves A.a {
  initial state Isus 
  {
   match message with
    * => {fail.}
   end
  }
 }

}

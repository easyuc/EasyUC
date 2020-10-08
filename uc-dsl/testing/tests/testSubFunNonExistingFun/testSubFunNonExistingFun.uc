direct a {
in x@bla()
}

direct A {a:a}

functionality R() implements A {

 subfun SF=Q

 party P serves A.a {
  initial state Isus 
  {
   match message with
    * => {fail.}
   end
  }
 }
}

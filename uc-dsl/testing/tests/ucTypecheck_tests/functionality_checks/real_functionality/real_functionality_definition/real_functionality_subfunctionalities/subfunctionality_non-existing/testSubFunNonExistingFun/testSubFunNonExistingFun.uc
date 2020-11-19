direct A_ {
in x@bla()
}

direct A {A:A_}

functionality R() implements A {

 subfun SF=Q

 party P serves A.A {
  initial state Isus 
  {
   match message with
    * => {fail.}
   end
  }
 }
}

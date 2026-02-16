uc_requires X.
uc_clone X.

direct A' {
in x@bla()
}

direct A {A:A'}

functionality R() implements A {

 subfun SF=X.Q

 party P serves A.A {
  initial state Isus 
  {
   match message with
    * => {fail.}
   end
  }
 }
}

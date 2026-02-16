uc_requires X.
uc_clone X as X1.

direct A' {
in x@bla()
}

direct A {A:A'}

adversarial D {
in bli()
}

functionality R(Q:X1.A) implements A {

 subfun Q=X1.S

 party P serves A.A {
  initial state Isus 
  {
   match message with
    * => {fail.}
   end
  }
 }

}

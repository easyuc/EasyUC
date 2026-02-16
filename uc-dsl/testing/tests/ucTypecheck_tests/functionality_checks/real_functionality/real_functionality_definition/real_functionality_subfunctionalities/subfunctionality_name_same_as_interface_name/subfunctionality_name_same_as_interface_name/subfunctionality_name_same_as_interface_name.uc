uc_requires X.
uc_clone X as X1.
uc_clone X as X2.

direct A' {
in x@bla()
}

direct A {A:A'}

adversarial D {
in bli()
}

functionality R(Q:X2.A) implements A {

 subfun A=X1.S

 party P serves A.A {
  initial state Isus 
  {
   match message with
    * => {fail.}
   end
  }
 }

}

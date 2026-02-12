uc_requires X.
uc_clone X as X1.
uc_clone X as X2.

direct D' {
in x@bla()
}

direct D {D:D'}

adversarial A {
in bla()
}

functionality R() implements D {

subfun SF=X1.Q
subfun SF=X2.Q

 party P serves D.D {
  initial state Isus 
  {
   match message with
    * => {fail.}
   end
  }
 }

}

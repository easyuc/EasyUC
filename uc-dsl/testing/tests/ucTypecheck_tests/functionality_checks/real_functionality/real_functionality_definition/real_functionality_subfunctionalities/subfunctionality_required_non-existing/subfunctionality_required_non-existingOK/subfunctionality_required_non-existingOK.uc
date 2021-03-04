uc_requires Req.

direct A' {
in x@bla()
}

direct A {A:A'}

adversarial D {
in bli()
}

functionality R(Q:A) implements A {

 subfun R'=Req.S

 party P serves A.A {
  initial state Isus 
  {
   match message with
    * => {fail.}
   end
  }
 }

}

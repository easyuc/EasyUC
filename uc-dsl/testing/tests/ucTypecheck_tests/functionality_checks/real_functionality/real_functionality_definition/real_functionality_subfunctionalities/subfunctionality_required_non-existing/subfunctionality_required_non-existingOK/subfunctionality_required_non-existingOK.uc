uc_requires Req.
uc_clone Req as Req1.
uc_clone Req as Req2.

direct A' {
in x@bla()
}

direct A {A:A'}

adversarial D {
in bli()
}

functionality R(Q:Req2.A) implements A {

 subfun R'=Req1.S

 party P serves A.A {
  initial state Isus 
  {
   match message with
    * => {fail.}
   end
  }
 }

}

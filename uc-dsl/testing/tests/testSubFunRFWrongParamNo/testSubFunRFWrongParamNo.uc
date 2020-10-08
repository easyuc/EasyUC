direct a {
in x@bla()
}

direct A {a:a}

adversarial d{
in bli()
}

functionality Q() implements A d {
  initial state Isus 
  {
   match message with
    * => {fail.}
   end
  }
}

functionality R(F:A) implements A {

 subfun SF=Q(F)

 party P serves A.xa {
  initial state Isus 
  {
   match message with
    * => {fail.}
   end
  }
 }
}

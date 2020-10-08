direct a {
in x@bla()
}

adversarial d {
in bli()
}

direct A {a:a}

functionality Q implements A d{

initial state Isus 
  {
   match message with
    * => {fail.}
   end
  }
}

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

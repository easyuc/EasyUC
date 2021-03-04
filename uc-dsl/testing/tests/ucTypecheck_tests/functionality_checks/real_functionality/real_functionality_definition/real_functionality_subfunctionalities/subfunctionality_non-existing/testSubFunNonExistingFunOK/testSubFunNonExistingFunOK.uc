direct A' {
in x@bla()
}

adversarial D {
in bli()
}

direct A {A:A'}

functionality Q implements A D{

initial state Isus 
  {
   match message with
    * => {fail.}
   end
  }
}

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

direct a {
in x@bla()
}

direct A {A:a}

adversarial d {
in bli()
}



functionality S() implements A d{

  initial state Isus 
  {
   match message with
    * => {fail.}
   end
  }

}

functionality R(Q:A) implements A {

 subfun Q=S

 party P serves A.A {
  initial state Isus 
  {
   match message with
    * => {fail.}
   end
  }
 }

}

direct A' {
in x@bla()
}

direct A {A:A'}

adversarial D {
in bli()
}



functionality S() implements A D{

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

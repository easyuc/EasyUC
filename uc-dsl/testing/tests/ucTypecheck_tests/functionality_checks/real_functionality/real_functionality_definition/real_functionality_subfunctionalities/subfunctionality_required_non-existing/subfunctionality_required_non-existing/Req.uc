direct A_ {
in x@bla()
}

direct A {A:A_}

adversarial D {
in bli()
}


functionality S() implements A D {

  initial state Isus 
  {
   match message with
    * => {fail.}
   end
  }

}

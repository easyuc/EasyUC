direct A {
Bio:B
}

direct B {
in x@bla()
}





functionality S() implements A {
 party P serves Cio {
  initial state Is 
  {
   match message with
    othermsg => {fail.}
   end
  }
 }

}


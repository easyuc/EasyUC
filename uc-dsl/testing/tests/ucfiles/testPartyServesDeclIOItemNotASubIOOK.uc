direct A {
Bio:B
}

direct B {
in x@bla()
}

functionality S() implements A {
 party P serves Bio {
  initial state Is 
  {
   match message with
    othermsg => {fail.}
   end
  }
 }

}


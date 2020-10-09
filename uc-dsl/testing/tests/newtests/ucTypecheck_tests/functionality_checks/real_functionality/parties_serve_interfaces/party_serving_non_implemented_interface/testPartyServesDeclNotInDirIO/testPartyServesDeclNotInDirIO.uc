direct B {
in x@bla()
}

direct A {
Bio:B
}

direct C {
Bio:B
}

functionality S() implements A {
 party P serves C.Cio {
  initial state Is 
  {
   match message with
    * => {fail.}
   end
  }
 }

}


adversarial B {
in bla()
}

direct E{
in x@bla()
}

direct D {
Subio:E
Subio3:E
}

functionality S() implements D B {
  initial state Is 
  {
   match message with
    * => {fail.}
   end
  }
}

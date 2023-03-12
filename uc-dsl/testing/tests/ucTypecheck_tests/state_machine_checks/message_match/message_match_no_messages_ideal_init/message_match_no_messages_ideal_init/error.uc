adversarial B {
in bla()
}

direct E{
out bla()@x
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

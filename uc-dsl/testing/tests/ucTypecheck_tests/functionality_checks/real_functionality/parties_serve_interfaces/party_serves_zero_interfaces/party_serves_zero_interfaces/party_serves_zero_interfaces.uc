adversarial B {
in bla()
}

adversarial A {
Subio:B

}

direct E{
in x@bla()
}

direct D {
Subio:E
}

functionality S() implements D A {
 party P1 serves {
  initial state Is 
  {
   match message with
    * => {fail.}
   end
  }
 }
}


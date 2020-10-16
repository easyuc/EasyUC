adversarial B {
in bla()
}

adversarial A {
subio:B

}

direct E{
in x@bla()
}

direct D {
subio:E
}

functionality S() implements D A {
 party P1 serves D.subio A.subio {
  initial state Is 
  {
   match message with
    * => {fail.}
   end
  }
 }
}


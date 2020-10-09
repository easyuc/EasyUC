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
subio2:E
subio3:E
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

 party P2 serves D.subio2 {
  initial state Is 
  {
   match message with
    * => {fail.}
   end
  }
 }

 party P3 serves D.subio3 {
  initial state Is 
  {
   match message with
    * => {fail.}
   end
  }
 }

}


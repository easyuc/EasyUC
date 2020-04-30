adversarial A {
subio:B

}

adversarial B {
in bla()
}

direct D {
subio:E
subio2:E
subio3:E
}

direct E{
in x@bla()
}

functionality S() implements D A {
 party P1 serves D.subio,A.subio {
  initial state Is 
  {
   match message with
    othermsg => {fail.}
   end
  }
 }

 party P2 serves D.subio2,D.subio3 {
  initial state Is 
  {
   match message with
    othermsg => {fail.}
   end
  }
 }

}


adversarial A {
subio:B

}

adversarial B {
in bla()
}

direct D {
subio:E
}

direct E{
in x@bla()
}

functionality S() implements D A {
 party P1 serves D.subio {
  initial state Is 
  {
   match message with
    othermsg => {fail.}
   end
  }
 }

 party P2 serves A.subio {
  initial state Is 
  {
   match message with
    othermsg => {fail.}
   end
  }
 }

}


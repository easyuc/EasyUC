adversarial B {
in bla()
}

adversarial A {
Subio:B
Subio2:B
}

direct E{
in x@bla()
}

direct D {
Subio:E
}

functionality S() implements D A {
 party P1 serves A.Subio2 D.Subio A.Subio {
  initial state Is 
  {
   match message with
    * => {fail.}
   end
  }
 }

 party P2 serves D.Subio2 A.Subio {
  initial state Is 
  {
   match message with
    * => {fail.}
   end
  }
 }

}


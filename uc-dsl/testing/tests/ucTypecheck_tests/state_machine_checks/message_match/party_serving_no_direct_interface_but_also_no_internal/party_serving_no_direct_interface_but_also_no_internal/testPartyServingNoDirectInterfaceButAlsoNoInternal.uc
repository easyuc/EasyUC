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
Subio3:E
}

functionality S() implements D A {
 party P1 serves D.Subio {
  initial state Is 
  {
   match message with
    * => {fail.}
   end
  }
 }

 party P2 serves A.Subio {
  initial state Is 
  {
   match message with
     * => { fail. }
   end
  }
 }

 party P3 serves D.Subio3 {
  initial state Is 
  {
   match message with
    * => {fail.}
   end
  }
 }

}

uc_requires V.
uc_clone V.

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
 subfun SF = V.SF

 party P1 serves D.Subio A.Subio {
  initial state Is 
  {
   match message with
    * => {fail.}
   end
  }
 }

 party P2 serves {
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

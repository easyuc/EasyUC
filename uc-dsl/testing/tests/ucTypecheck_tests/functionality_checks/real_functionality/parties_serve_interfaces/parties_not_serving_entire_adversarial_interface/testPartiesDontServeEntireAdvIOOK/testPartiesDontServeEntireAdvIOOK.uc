adversarial B {
in m()
}

adversarial A {
Bio1:B
Bio2:B
}

direct C {in x@m()}

direct D {
C1:C
C2:C
}

functionality S() implements D A {
 party P1 serves D.C1 A.Bio1 {
  initial state Is 
  {
   match message with
    *  => {fail.}
   end
  }
 }

 party P2 serves D.C2 A.Bio2 {
  initial state Is 
  {
   match message with
    * => {fail.}
   end
  }
 }

}


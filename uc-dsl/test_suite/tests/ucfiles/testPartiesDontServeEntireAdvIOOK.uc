adversarial A {
Bio1:B
Bio2:B
}

adversarial B {
in m()
}

direct C {in x@m()}

direct D {
C1:C
C2:C
}

functionality S() implements D A {
 party P1 serves C1,Bio1 {
  initial state Is 
  {
   match message with
    othermsg => {fail.}
   end
  }
 }

 party P2 serves C2,Bio2 {
  initial state Is 
  {
   match message with
    othermsg => {fail.}
   end
  }
 }

}


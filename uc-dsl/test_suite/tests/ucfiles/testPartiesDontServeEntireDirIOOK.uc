direct A {
Bio1:B
Bio2:B
}

direct B {
in x@m()
}

functionality S() implements A {
 party P1 serves Bio1 {
  initial state Is 
  {
   match message with
    othermsg => {fail.}
   end
  }
 }

 party P2 serves Bio2 {
  initial state Is 
  {
   match message with
    othermsg => {fail.}
   end
  }
 }

}


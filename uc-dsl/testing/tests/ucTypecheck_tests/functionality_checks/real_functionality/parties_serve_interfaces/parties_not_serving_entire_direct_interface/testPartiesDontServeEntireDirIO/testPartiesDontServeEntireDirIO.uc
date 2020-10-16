direct B {
in x@m()
}

direct A {
Bio1:B
Bio2:B
Bio3:B
}

functionality S implements A {
 party P1 serves A.Bio1 {
  initial state Is 
  {
   match message with
    * => {fail.}
   end
  }
 }

 party P2 serves A.Bio2 {
  initial state Is 
  {
   match message with
    * => {fail.}
   end
  }
 }

}


direct A' {
in x@bla()
}

direct A {A:A'}

functionality F() implements A {
 party P serves A.A {
  state S() 
  {
   match message with
    * => {fail.}
   end
  }
 }
}


direct a {
in x@bla()
}

direct A {A:a}

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


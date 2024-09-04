direct A' {
in x@bla()
out bli@x
}

direct A {A:A'}

functionality F() implements A {
 party P serves A.A {
  initial state S
  {
   match message with
    x@A.A.bla => {send A.A.bli@x and transition T.}
   end
  }

  state S() 
  {
   match message with
    * => {fail.}
   end
  }

 }
}


direct a {
in x@bla()
}

direct A {A:a}

functionality F() implements A {
 party P serves A.A {
  initial state S
  {
   match message with
    * => {fail.}
   end
  }

  state T(p:port)
  {
   var p:port;
   match message with
    * => {fail.}
   end
  }

 }
}


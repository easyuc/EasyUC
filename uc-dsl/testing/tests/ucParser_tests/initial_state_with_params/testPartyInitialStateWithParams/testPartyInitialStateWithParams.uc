direct A_ {
in x@bla()
}

direct A {A:A_}

functionality F() implements A {
 party P serves A.A {
  initial state S(p:port)
  {
   match message with
    * => {fail.}
   end
  }
 }
}


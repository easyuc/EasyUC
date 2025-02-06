direct A' {
in  x@bla()
out bli@x
}

direct A {A:A'}

adversarial B {
  in blah
  out blur(x : port)
}

functionality F() implements A B {
  initial state I {
   match message with
    sender@A.A.bla() =>
      {send B.blur(([],3)) and transition II(false).}
   end
  }
 
  state II(k:bool) {
   match message with
    * => {fail.}
   end
  }
}

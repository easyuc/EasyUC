direct A' {
in  x@bla()
out bli(y : port)@x
}

direct A {A:A'}

functionality F() implements A {

 party P serves A.A {

  initial state I {
   match message with
    sender@A.A.bla() => {send A.A.bli(intport Q)@sender and transition II(false).}
   end
  }
 
  state II(k:bool) {
   match message with
    * => {fail.}
   end
  }
 }
}

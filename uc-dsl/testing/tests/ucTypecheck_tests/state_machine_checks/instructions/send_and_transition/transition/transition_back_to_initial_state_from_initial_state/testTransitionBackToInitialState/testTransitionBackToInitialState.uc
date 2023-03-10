direct A' {
in  x@bla()
out bli()@x
}

direct A {A:A'}

functionality F() implements A {

 party P serves A.A {

  initial state I {
   match message with
    sender@A.A.bla() => {send A.A.bli()@sender and transition I.}
   end
  }

  state J { match message with * => { fail. } end }
 }
}

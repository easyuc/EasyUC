direct A_ {
in  x@bla()
out bli()@x
}

direct A {A:A_}

functionality F() implements A {

 party P serves A.A {

  initial state I {
   match message with
    x@A.A.bla => {send A.A.bli()@x and transition I.}
   end
  }
 }
}

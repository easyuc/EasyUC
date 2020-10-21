direct a {
in  x@bla()
out bli()@x
}

direct A {A:a}

functionality F() implements A {

 party P serves A.A {

  initial state I {
   match message with
    A.A.*  => {send A.A.bli() and transition I.}
   end
  }
 }
}

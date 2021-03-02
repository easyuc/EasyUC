ec_requires +IntInt.

direct A' {
in  x@bla()
out bli()@x
}

direct A {A:A'}

functionality F() implements A {

 party P serves A.A {

  initial state I {
   var i_1,i_2:int;
   match message with
    sender@A.A.bla() => {(i_1,i_2)<-intint; fail.}
   end
  }
 }
}

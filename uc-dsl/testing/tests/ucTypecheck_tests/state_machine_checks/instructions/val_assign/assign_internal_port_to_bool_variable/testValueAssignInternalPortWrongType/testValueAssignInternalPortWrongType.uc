direct A' {
in  x@bla()
out bli()@x
}

direct A {A:A'}

functionality F(G:A) implements A {

 party P serves A.A {

  initial state I {
   var x : bool;
   match message with
     y@A.A.bla => { x<-intport P; fail. }
   | * => { fail. }
   end
  }
 }
}

direct A_ {
in  x@bla()
out bli()@x
}

direct A {A:A_}

functionality F(G:A) implements A {

 party P serves A.A {

  initial state I {
   var x : bool;
   match message with
    *  => { x<-intport P; fail. }
   end
  }
 }
}

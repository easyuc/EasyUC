direct a {
in  x@bla()
out bli()@x
}

direct A {A:a}

functionality F(G:A) implements A {

 party P serves A.A {

  initial state I {
   var x : bool;
   match message with
    *  => { x<-P; fail. }
   end
  }
 }
}

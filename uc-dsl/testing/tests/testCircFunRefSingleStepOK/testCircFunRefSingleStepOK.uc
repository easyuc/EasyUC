direct a {
in x@bla()
}

direct A {a:a}

functionality F() implements A {

 party P serves A.a {
  initial state Isus 
  {
   match message with
    |*  => {fail.}
   end
  }
 }
}

functionality R() implements A {

subfun SF=F

 party P serves A.a {
  initial state Isus 
  {
   match message with
    |*  => {fail.}
   end
  }
 }
}

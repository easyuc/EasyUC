direct a {
in x@bla()
}

direct A {a:a}

functionality F() implements A {

 party P serves a {
  initial state Isus 
  {
   match message with
    othermsg => {fail.}
   end
  }
 }
}

functionality R() implements A {

subfun SF=F()

 party P serves a {
  initial state Isus 
  {
   match message with
    othermsg => {fail.}
   end
  }
 }
}

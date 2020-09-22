direct a {
in x@bla()
}

direct A {a:a}

functionality R() implements A {

 subfun SF=Q()

 party P serves a {
  initial state Isus 
  {
   match message with
    othermsg => {fail.}
   end
  }
 }
}

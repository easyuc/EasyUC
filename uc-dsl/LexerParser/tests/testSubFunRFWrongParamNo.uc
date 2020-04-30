direct a {
in x@bla()
}

direct A {a:a}

functionality Q() implements A {
 party P serves a {
  initial state Isus 
  {
   match message with
    othermsg => {fail.}
   end
  }
 }
}

functionality R(F:A) implements A {

 subfun SF=Q(F)

 party P serves a {
  initial state Isus 
  {
   match message with
    othermsg => {fail.}
   end
  }
 }
}

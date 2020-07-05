direct a {
in x@bla()
}

direct A {a:a}

functionality R() implements A {

subfun SF=Q()

 party P serves a {
  initial state Is
  {
   match message with
    othermsg => {fail.}
   end
  }
 }
}

functionality Q() implements A {

subfun SF=R()

 party P serves a {
  initial state Is
  {
   match message with
    othermsg => {fail.}
   end
  }
 }
}

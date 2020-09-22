direct a {
in x@bla()
}

direct A {a:a}

functionality F() implements A {

 party P serves a {
  initial state Is
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

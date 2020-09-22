direct a {
in x@bla()
}

direct A {a:a}

functionality R implements A{

party P serves a {
  initial state Is
  {
   match message with
    othermsg => {fail.}
   end
  }
 }
}

functionality Q() implements R {

 party P serves a {
  initial state Is
  {
   match message with
    othermsg => {fail.}
   end
  }
 }
}


direct a {
in x@bla()
}

direct A {A:a}

functionality F() implements A {
 party P serves A {
  initial state S
  {
   match message with
    othermsg => {fail.}
   end
  }

  state T(p:port)
  {
   var q:port;
   match message with
    othermsg => {fail.}
   end
  }

 }
}


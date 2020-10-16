direct a {
in x@bla()
}

direct A {A:a}

functionality F() implements A {
 party P serves A.A {
  initial state S
  {
   match message with
    * => {fail.}
   end
  }

  state T()
  {
   var p:port; var q:qort;
   match message with
    * => {fail.}
   end
  }

 }
}


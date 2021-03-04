direct A' {
in x@bla()
}

direct A {A:A'}

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


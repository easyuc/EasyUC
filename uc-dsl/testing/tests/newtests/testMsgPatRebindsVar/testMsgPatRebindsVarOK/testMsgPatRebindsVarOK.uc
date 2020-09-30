direct a {
in x@bla()
}

adversarial b {
in bla(p:port)
}

direct A {a:a}

functionality F implements A b {

  initial state Is 
  {
   var P:port;
   match message with
    b.bla(p) => {fail.}
   | *       => {fail.}
   end
  }

}

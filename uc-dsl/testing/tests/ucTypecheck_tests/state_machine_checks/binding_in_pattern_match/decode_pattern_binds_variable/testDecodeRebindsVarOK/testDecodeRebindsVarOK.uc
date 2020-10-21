direct a {
in x@bla(u:univ)
}

adversarial b {
in bla()
}

direct A {a:a}

functionality F implements A b {

  initial state Is 
  {
   var P:port;
   match message with
    p@A.a.bla(u) => {
          decode u as port with
          | ok pt => { fail. }
          | error => { fail. }
          end
        }
   | *       => {fail.}
   end
  }

}

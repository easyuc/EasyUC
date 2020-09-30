direct a {
in x@bla()
}

adversarial b {
in bla(u:univ)
}

direct A {a:a}

functionality F implements A b {

  initial state Is 
  {
   match message with
    b.bla(u) => {
          decode u as bool * bool  with
          | ok (b,b)  => { fail. }
          | error     => { fail. }
          end
        }
   | *       => {fail.}
   end
  }

}

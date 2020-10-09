direct a {
in x@bla(u:univ)
}

direct A {a:a}

functionality F implements A {

 party P serves A.a {

  initial state Is 
  {
   match message with
    p@A.a.bla(u) => {
          decode u as port with
          | ok p  => { fail. }
          | error => { fail. }
          end
        }
   end
  }

 }

}

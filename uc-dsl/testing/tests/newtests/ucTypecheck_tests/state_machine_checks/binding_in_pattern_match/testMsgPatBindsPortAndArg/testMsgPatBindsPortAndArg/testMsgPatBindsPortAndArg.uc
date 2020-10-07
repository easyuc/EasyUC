direct a {
in x@bla(p:port)
}

direct A {a:a}

functionality F implements A {

 party P serves A.a {

  initial state Is 
  {
   match message with
    p@A.a.bla(p) => {fail.}
   end
  }

 }

}

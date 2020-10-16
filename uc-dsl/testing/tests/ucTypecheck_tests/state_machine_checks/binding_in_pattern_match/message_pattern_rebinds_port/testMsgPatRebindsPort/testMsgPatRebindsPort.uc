direct a {
in x@bla()
}

direct A {a:a}

functionality F implements A {

 party P serves A.a {

  initial state Is 
  {
   match message with
    P@A.a.bla => {fail.}
   end
  }

 }

}

direct a {
in x@bla()
}

direct A {a:a}

functionality F implements A {

 party P serves A.a {

  initial state Is 
  {
   match message with
    * => {fail.}
   end
  }

  state S(P:bool) 
  {
   match message with
    * => {fail.}
   end
  }

 }

}

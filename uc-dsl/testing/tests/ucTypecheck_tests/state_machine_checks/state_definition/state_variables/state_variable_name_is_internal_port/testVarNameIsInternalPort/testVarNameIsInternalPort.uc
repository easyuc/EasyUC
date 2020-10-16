direct a {
in x@bla()
}

direct A {a:a}

functionality F implements A {

 party P serves A.a {

  initial state Is 
  {
   var P:bool;
   match message with
    * => {fail.}
   end
  }
 }

}

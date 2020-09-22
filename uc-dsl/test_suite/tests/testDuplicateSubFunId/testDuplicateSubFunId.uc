direct a {
in x@bla()
}

direct A {a:a}

functionality Q() implements A {

 party P serves a {
  initial state Is 
  {
   match message with
    othermsg => {fail.}
   end
  }
 }


}

functionality R() implements A {

subfun SF=Q()
subfun SF=Q()

 party P serves a {
  initial state Isus 
  {
   match message with
    othermsg => {fail.}
   end
  }
 }

}

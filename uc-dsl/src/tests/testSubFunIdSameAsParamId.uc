direct a {
in x@bla()
}

direct A {A:a}

direct d {
in x@bli()
}

direct D {D:d}



functionality S() implements A {
 party P serves A {
  initial state Isus 
  {
   match message with
    othermsg => {fail.}
   end
  }
 }

}

functionality R(Q:A) implements A {

 subfun Q=S()

 party P serves A {
  initial state Isus 
  {
   match message with
    othermsg => {fail.}
   end
  }
 }

}

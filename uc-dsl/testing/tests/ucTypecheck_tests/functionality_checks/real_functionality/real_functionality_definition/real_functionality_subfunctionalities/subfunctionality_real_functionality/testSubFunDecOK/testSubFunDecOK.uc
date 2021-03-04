adversarial Adv' {
in bla()
}

adversarial Adv {Adv:Adv'}

direct D' {

in x@bla()
}

direct D {D:D'}

functionality F implements D Adv' {

  initial state Is
  {
   match message with
    | * => { fail. }
   end
  }
 }

functionality R() implements D{

subfun SF=F

 party P serves D.D {
  initial state Is
  {
   match message with
    | * => {fail.}
   end
  }
 }
}


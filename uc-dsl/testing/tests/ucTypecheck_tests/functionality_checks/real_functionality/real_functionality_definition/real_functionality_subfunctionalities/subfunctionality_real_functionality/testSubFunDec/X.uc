adversarial Adv' {
  in bla()
}

adversarial Adv {Adv:Adv'}

direct D' {
  in x@bla()
}

direct D {D:D'}

functionality F implements D Adv {

 party P serves D.D Adv.Adv {
  initial state Is
  {
   match message with
    | * => { fail. }
   end
  }
 }
}

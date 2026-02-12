adversarial Adv' {
  in bla()
}

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

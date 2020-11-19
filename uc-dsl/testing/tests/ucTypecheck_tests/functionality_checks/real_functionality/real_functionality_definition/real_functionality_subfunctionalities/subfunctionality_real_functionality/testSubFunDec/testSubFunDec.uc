adversarial Adv_ {
in bla()
}

adversarial Adv {Adv:Adv_}

direct D_ {

in x@bla()
}

direct D {D:D_}

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


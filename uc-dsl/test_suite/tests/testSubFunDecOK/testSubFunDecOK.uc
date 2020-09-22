adversarial adv {
in bla()
}

adversarial Adv {adv:adv}

direct d {

in x@bla()
}

direct D {d:d}

functionality F implements D adv {

  initial state Is
  {
   match message with
    | * => { fail. }
   end
  }
 }

functionality R() implements D{

subfun SF=F

 party P serves D.d {
  initial state Is
  {
   match message with
    | * => {fail.}
   end
  }
 }
}


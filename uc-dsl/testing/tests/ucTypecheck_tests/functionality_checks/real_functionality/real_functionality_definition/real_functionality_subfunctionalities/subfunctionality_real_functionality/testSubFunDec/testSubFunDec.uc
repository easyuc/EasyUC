uc_requires X.
uc_clone X.

adversarial Adv' {
in bla()
}

direct D' {

in x@bla()
}

direct D {D:D'}

functionality R() implements D{

subfun SF=X.F

 party P serves D.D {
  initial state Is
  {
   match message with
    | * => {fail.}
   end
  }
 }
}


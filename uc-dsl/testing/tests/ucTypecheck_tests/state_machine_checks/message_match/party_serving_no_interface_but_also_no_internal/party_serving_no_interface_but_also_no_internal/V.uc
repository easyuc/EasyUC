direct X { in pt@hi out bye@pt }
direct XX {X : X}

adversarial Y { in bye out hi }

functionality SF implements XX Y {
  initial state IS {
    match message with
      pt@XX.X.hi => { send Y.hi and transition NS(pt). }
    end
  }

  state NS(pt : port) {
    match message with
      Y.bye => { send XX.X.bye@pt and transition NS(pt). }
    | *     => { fail. }
    end
  }
}

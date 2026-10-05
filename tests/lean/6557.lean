/-! Test explicit inaccessible patterns variables -/

example : (x : Bool × Bool) → x.fst = x.snd ⊕' Unit → Unit
  | (.(b), b), .inl rfl => ()
  | (_, false), _ => ()
  | (_, true), _ => ()

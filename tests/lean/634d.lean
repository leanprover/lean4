open nat
section
  universe l
  definition A {n : ℕ} (t : Type.{l}) := t
  check A
  check _root_.A.{1}
  set_option pp.universes true
  check A
  check _root_.A.{1}
end

section
  universe l
  parameters {B : Type.{l}}
  definition P {n : ℕ} (b : B) := b
  check P
  check @_root_.P.{1} nat
  set_option pp.universes true
  check P
  check _root_.P.{1}
  set_option pp.implicit true
  check @P 2
  check @_root_.P.{1} nat
end

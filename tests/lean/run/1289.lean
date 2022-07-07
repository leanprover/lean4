def _root_.Nat.mod2 : Nat → Nat
  | n+2 => n.mod2
  | n => n

protected def _root_.Nat.mod3 : Nat → Nat
  | n+2 => n.mod3
  | n => n

private def _root_.Nat.mod4 : Nat → Nat
  | n+2 => n.mod4
  | n => n

#exit

inductive Foo.Bla.T where
  | s : T → T
  | z

namespace AAA.BBB.CCC

def _root_.Foo.Bla.T.toNat₁ : Foo.Bla.T → Nat
  | .s a => a.toNat₁ + 1
  | .z => 0

protected def _root_.Foo.Bla.T.toNat₂ : Foo.Bla.T → Nat
  | .s a => a.toNat₂ + 1
  | .z => 0

private def _root_.Foo.Bla.T.toNat₃ : Foo.Bla.T → Nat
  | .s a => a.toNat₃ + 1
  | .z => 0

def _root_.Foo.Bla.T.toNat₄ : Foo.Bla.T → Nat
  | .s a => toNat₄ a + 1
  | .z => 0

protected def _root_.Foo.Bla.T.toNat₅ : Foo.Bla.T → Nat
  | .s a => T.toNat₅ a + 1
  | .z => 0

private def _root_.Foo.Bla.T.toNat₆ : Foo.Bla.T → Nat
  | .s a => toNat₆ a + 1
  | .z => 0

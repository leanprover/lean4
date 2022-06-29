inductive Sign where
  | zero | neg | pos
  deriving DecidableEq

instance : OfNat Sign (nat_lit 0) where
  ofNat := .zero

instance : OfNat Sign (nat_lit 1) where
  ofNat := .pos

instance : Neg Sign where
  neg | .zero => .zero
      | .pos  => .neg
      | .neg  => .pos

namespace Sign

@[simp] theorem zero_eq : zero = 0 := rfl
@[simp] theorem neg_eq : neg  = -1 := rfl
@[simp] theorem pos_eq : pos = 1 := rfl

def mul : Sign → Sign → Sign
  | neg,  neg  => pos
  | neg,  pos  => neg
  | neg,  zero => zero
  | zero, _    => zero
  | pos,  s    => s

instance : Mul Sign where
  mul a b := Sign.mul a b

def le : Sign → Sign → Bool
  | neg,  _    => true
  | zero, zero => true
  | _,    pos  => true
  | _,    _    => false

instance : LE Sign where
  le a b := Sign.le a b

instance : DecidableRel (· ≤ · : Sign → Sign → Prop) :=
  fun a b => inferInstanceAs (Decidable (le a b = true))

theorem neg_bot {s : Sign} : s ≤ -1 → s = -1 := by
  cases s <;> decide

theorem pos_top {s : Sign} : 1 ≤ s → s = 1 := by
  cases s <;> decide

end Sign

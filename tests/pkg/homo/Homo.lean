import Homo.Init

set_option warn.sorry false

opaque TSpec (_ : Nat) : (α : Type) × α := ⟨Unit, ()⟩
def T (x : Nat) : Type := (TSpec x).1
instance : Inhabited (T x) := ⟨TSpec x |>.2⟩
opaque toInt : T n → Int
@[grind_homo_pred] axiom toInt_bounds (x : T n) : 0 <= toInt x ∧ toInt x < 2^n

opaque add : T n → T n → T n
opaque le : T n → T n → Prop
opaque pos : T n → Prop
opaque small : T n → Prop
opaque f (n : Nat) : Nat → T n

@[grind_homo] theorem T.eq (a b : T n) : a = b ↔ toInt a = toInt b := sorry
@[grind_homo] theorem T.le (a b : T n) : le a b ↔ toInt a ≤ toInt b := sorry
@[grind_homo] theorem T.pos (a : T n) : pos a ↔ toInt a > 0 := sorry
@[grind_homo] theorem T.small (a : T n) : small a ↔ toInt a < 8 := sorry
@[grind_homo] theorem T.add (a b : T n) : toInt (add a b) = (toInt a + toInt b) % 128 := sorry
@[grind_homo] theorem cleanLeft (a b n : Int) : (a % n + b) % n = (a + b) % n := by simp
@[grind_homo] theorem cleanRight (a b n : Int) : (a + b % n) % n = (a + b) % n := by simp

-- set_option trace.homo true
set_option trace.homo.pred true
-- set_option trace.grind.assert true
example (b : T 7) : pos b → small b →
    small (f 7 (0 + d + a + 1)) → pos (f 7 (0 + d + a + 1)) → small c → pos c → let x := b; le b (add c (add x (f 7 (0 + d + a + 1)))) := by
  grind

example (x : Int) : 0 ≤ x → x < 2 → (2*x) % 128 = x → x = 0 := by
  grind

example (b : T 1) (h : add b b = b) : toInt b = 0 := by
  grind

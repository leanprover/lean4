@[coe] def Bool.toNat' : Bool → Nat
  | true => 1
  | false => 0

instance : Coe Bool Nat where
  coe := Bool.toNat'

@[norm_cast] theorem ofNat_band (a b : Bool) : (↑(a && b) : Nat) = ↑a &&& ↑b := by
  cases a <;> cases b <;> rfl

example (a b c : Bool) (n : Nat) (h : n = a &&& b &&& c)
        : (↑(a && b && c) : Nat) = n := by
  push_cast
  guard_target =ₛ(↑a &&& ↑b &&& ↑c) = n
  rw [h]

example (a b c : Bool) (n : Nat) (h : n = (a && b && c))
        : (↑a &&& ↑b &&& ↑c) = n := by
  norm_cast
  guard_target =ₛ ↑(a && b && c) = n
  rw [h]


set_option linter.missingDocs false

variable (an bn cn dn : Nat) (az bz cz dz : Int)

example : (an : Int) = bn → an = bn := by intro h; exact_mod_cast h
example : an = bn → (an : Int) = bn := by intro h; exact_mod_cast h

example : (an : Int) < bn ↔ an < bn := by norm_cast
example : (an : Int) ≠ (bn : Int) ↔ an ≠ bn := by norm_cast

-- zero and one cause special problems
example : az > (1 : Nat) ↔ az > 1 := by norm_cast
example : az > (0 : Nat) ↔ az > 0 := by norm_cast

example : (an : Int) ≠ 0 ↔ an ≠ 0 := by norm_cast

example (a b : Nat) (h : False) : (a : Int) < ((2 * b : Nat) : Int) := by
  push_cast
  guard_target = (a : Int) < 2 * (b : Int)
  cases h

example : (an : Int) + bn = (an + bn : Nat) := by norm_cast

example (h : ((an + bn : Nat) : Int) = (an : Int) + (bn : Int)) : True := by
  push_cast at h
  guard_hyp h : (an : Int) + (bn : Int) = (an : Int) + (bn : Int)
  trivial

example (h : ((an * bn : Nat) : Int) = (an : Int) * (bn : Int)) : True := by
  push_cast at h
  guard_hyp h : (an : Int) * (bn : Int) = (an : Int) * (bn : Int)
  trivial

--testing numerals
example : ((42 : Nat) : Int) = 42 := by norm_cast

structure p (n : Int)
example : p 42 := by
  norm_cast
  guard_target = p 42
  exact ⟨⟩

example : an + bn = 1 ↔ (an + bn : Int) = 1 := by norm_cast

example (h : bn ≤ an) : an - bn = 1 ↔ (an - bn : Int) = 1 := by norm_cast

example (k : Nat) {x y : Nat} (h : ((x + y + k : Nat) : Int) = 0) : x + y + k = 0 := by
  push_cast at h
  guard_hyp h : (x : Int) + y + k = 0
  assumption_mod_cast

example (a b : Nat) (h2 : ((a + b + 0 : Nat) : Int) = 10) :
    ((a + b : Nat) : Int) = 10 := by
  push_cast
  push_cast [Int.add_zero] at h2
  exact h2

theorem b (_h g : true) : true ∧ true := by
  constructor
  assumption_mod_cast
  assumption_mod_cast

example : ¬n - k + 1 = 0 := by
  norm_cast

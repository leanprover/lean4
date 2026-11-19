example (x y z : Nat) : x + y + 0 + z = z + (x + y) := by ac_rfl

example (x y z : Nat) : (x + y) * (0 + z) = (x + y) * z:= by ac_rfl

example (x y z : Nat) : (x + y) * (0 + z) = 1 * z * (y + 0 + x) := by ac_rfl

theorem ex₁ (x y z : Nat) : max (0 + (max x (max z (max (0 + 0) ((max 1 0) + 0 + 0) * y)))) y = max (max x y) z := by ac_rfl

#print ex₁

example (x y : Nat) : 1 + 0 + 0 = 0 + 1 := by ac_rfl

example (x y : Nat) : (x + y = 42) = (y + x = 42) := by ac_rfl

example (x y : Nat) (P : Prop) : (x + y = 42 → P) = (y + x = 42 → P) := by ac_rfl

inductive Vector' (α : Type u) : Nat → Type u where
  | nil  : Vector' α 0
  | cons : α → Vector' α n → Vector' α (n+1)

def f (n : Nat) (xs : Vector' α n) := xs

-- Repro: Dependent types trigger incorrect proofs
theorem ex₂ (n m : Nat) (xs : Vector' α (n+m)) (ys : Vector' α (m+n)) : (f (n+m) xs, f (m+n) ys, n+m) = (f (n+m) xs, f (m+n) ys, m+n) := by
  ac_rfl

-- Repro: Binders also trigger invalid proofs
theorem ex₃ (n : Nat) : (fun x => n + x) = (fun x => x + n) := by
  ac_rfl
#print ex₃

-- Repro: the Prop universe doesn't work
example (p q : Prop) : (p ∨ p ∨ q ∧ True) = (q ∨ p) := by
  ac_rfl

-- Repro: missing withContext
example : ∀ x : Nat, x = x := by intro x; ac_rfl

example : [1, 2] ++ ([] ++ [2+4, 8] ++ [4]) = [1, 2] ++ [4+2, 8] ++ [4] := by ac_rfl

/- BitVec arithmetic | commutativity -/

example (a b c d : BitVec w) :
    a * b * c * d = d * c * b * a := by
  ac_nf

example (a b c d : BitVec w) :
    a * b * c * d = d * c * b * a := by
  ac_rfl

example (a b c d : BitVec w) :
    a + b + c + d = d + c + b + a := by
  ac_nf

example (a b c d : BitVec w) :
    a + b + c + d = d + c + b + a := by
  ac_rfl

/- BitVec arithmetic | associativity -/

example (a b c d : BitVec w) :
    a * (b * (c * d)) = ((a * b) * c) * d := by
  ac_nf

example (a b c d : BitVec w) :
    a * (b * (c * d)) = ((a * b) * c) * d := by
  ac_rfl

example (a b c d : BitVec w) :
    a + (b + (c + d)) = ((a + b) + c) + d := by
  ac_nf

example (a b c d : BitVec w) :
    a + (b + (c + d)) = ((a + b) + c) + d := by
  ac_rfl

/- BitVec bitwise operations | commutativity -/

example (a b c d : BitVec w) :
    a ^^^ b ^^^ c ^^^ d = d ^^^ c ^^^ b ^^^ a := by
  ac_nf

example (a b c d : BitVec w) :
    a ^^^ b ^^^ c ^^^ d = d ^^^ c ^^^ b ^^^ a := by
  ac_rfl

example (a b c d : BitVec w) :
    a &&& b &&& c &&& d = d &&& c &&& b &&& a := by
  ac_nf

example (a b c d : BitVec w) :
    a &&& b &&& c &&& d = d &&& c &&& b &&& a := by
  ac_rfl

example (a b c d : BitVec w) :
    a ||| b ||| c ||| d = d ||| c ||| b ||| a := by
  ac_nf

example (a b c d : BitVec w) :
    a ||| b ||| c ||| d = d ||| c ||| b ||| a := by
  ac_rfl

/- BitVec bitwise operations | associativity -/

example (a b c d : BitVec w) :
    a &&& (b &&& (c &&& d)) = ((a &&& b) &&& c) &&& d := by
  ac_nf

example (a b c d : BitVec w) :
    a &&& (b &&& (c &&& d)) = ((a &&& b) &&& c) &&& d := by
  ac_rfl

example (a b c d : BitVec w) :
    a ||| (b ||| (c ||| d)) = ((a ||| b) ||| c) ||| d := by
  ac_nf

example (a b c d : BitVec w) :
    a ||| (b ||| (c ||| d)) = ((a ||| b) ||| c) ||| d := by
  ac_rfl

example (a b c d : BitVec w) :
    a ^^^ (b ^^^ (c ^^^ d)) = ((a ^^^ b) ^^^ c) ^^^ d := by
  ac_nf

example (a b c d : BitVec w) :
    a ^^^ (b ^^^ (c ^^^ d)) = ((a ^^^ b) ^^^ c) ^^^ d := by
  ac_rfl

example (a b c d : Nat) : a + b + c + d = d + (b + c) + a := by
  ac_nf

example (a b c d : Nat) (h₁ h₂ : a + b + c + d = d + (b + c) + a) :
    a + b + c + d = a + (b + c) + d := by

  ac_nf at h₁
  guard_hyp h₁ :ₛ a + (b + (c + d)) = a + (b + (c + d))

  guard_hyp h₂ :ₛ a + b + c + d = d + (b + c) + a
  ac_nf at h₂
  guard_hyp h₂ :ₛ a + (b + (c + d)) = a + (b + (c + d))

  ac_nf at *

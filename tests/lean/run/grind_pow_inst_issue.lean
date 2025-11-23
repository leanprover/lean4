theorem square_mod_eight_eq (n : Nat) :
    n ^ 2 % 8 = 0 ∨ n ^ 2 % 8 = 1 ∨ n ^ 2 % 8 = 4 := by
  sorry

theorem test0 {n : Nat} (hn : n % 8 = 7) (a b c : Nat)
    (hl' : a ^ 2 + b ^ 2 + c ^ 2 = n) :
    False := by
  grind [square_mod_eight_eq] -- works

class Monoid (M : Type u) extends Mul M, One M where
  protected npow : Nat → M → M

instance Monoid.toNatPow {M : Type u} [Monoid M] : Pow M Nat :=
  ⟨fun x n ↦ Monoid.npow n x⟩

instance Int.instCommMonoid : Monoid Int where
  npow n x := x ^ n

theorem test1 {n : Nat} (hn : n % 8 = 7) (a b c : Nat)
    (hl' : a ^ 2 + b ^ 2 + c ^ 2 = n) :
    False := by
  grind [square_mod_eight_eq] -- should work

attribute [-instance] Lean.Grind.instCommRingInt in

theorem test2 {n : Nat} (hn : n % 8 = 7) (a b c : Nat)
    (hl' : a ^ 2 + b ^ 2 + c ^ 2 = n) :
    False := by
  grind [square_mod_eight_eq] -- works

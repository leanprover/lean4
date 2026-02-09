example : (@OfNat.ofNat (Fin (1 + 1)) 0 Fin.instOfNat) = (0 : Fin 2) := by
  grind

example {C : Type} (h : Fin 2 → C) :
    h (@OfNat.ofNat (Fin (1 + 1)) 0 Fin.instOfNat) = h 0 := by
  grind -- should work too

namespace Fin

protected def sum [Zero α] [Add α] (x : Fin n → α) : α :=
  foldr n (x · + ·) 0

theorem sum_succ [Zero α] [Add α] (x : Fin (n + 1) → α) : Fin.sum x = x 0 + Fin.sum (fun i => x i.succ) := sorry

protected def count (p : Fin n → Bool) : Nat :=
  Fin.sum (Bool.toNat ∘ p)

theorem count_succ (p : Fin (n + 1) → Bool) : Fin.count p =
    if p 0 then Fin.count (fun i => p i.succ) + 1 else Fin.count (fun i => p i.succ) := by
  -- This previously failed, reporting a false proposition `0 = 0`, which expanded to:
  -- `@Eq.{1} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (nat_lit 0)`
  -- This was fixed in https://github.com/leanprover/lean4/pull/10323
  grind [Fin.count, Function.comp_def, Fin.sum_succ]

end Fin

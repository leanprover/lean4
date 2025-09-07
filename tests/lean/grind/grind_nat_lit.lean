
namespace Fin

protected def sum [Zero α] [Add α] (x : Fin n → α) : α :=
  foldr n (x · + ·) 0

protected def count (p : Fin n → Bool) : Nat :=
  Fin.sum (Bool.toNat ∘ p)

theorem count_succ (p : Fin (n + 1) → Bool) : Fin.count p =
    if p 0 then Fin.count (fun i => p i.succ) + 1 else Fin.count (fun i => p i.succ) := by
  -- fails, reporting a false proposition `0 = 0`, which is:
  -- `@Eq.{1} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (nat_lit 0)`
  grind [Fin.count]
  -- (I don't expect `grind` to solve this as is without additional lemmas, but it shouldn't get stuck on `0 = 0`).

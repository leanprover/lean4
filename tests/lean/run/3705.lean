structure MonoidHom (M : Type _) (N : Type _) [Mul M] [Mul N] where
  toFun : M → N
  map_mul' : ∀ x y, toFun (x * y) = toFun x * toFun y

class CommMagma (G : Type _) extends Mul G where
  mul_comm : ∀ a b : G, a * b = b * a

set_option quotPrecheck false
infixr:25 " →*' " => MonoidHom

instance [Mul M] [Mul N] : CoeFun (M →*' N) (fun _ => M → N) where
  coe := MonoidHom.toFun

open CommMagma

-- -- this instance needed
instance MonoidHom.commMonoid [Mul M] [Mul N] :
    CommMagma (M →*' N) where
  mul := fun f g => { toFun := fun x => f x * g x, map_mul' := sorry }
  mul_comm := sorry


example {M} [Mul M] [Mul G] [Pow G Int] :
    let zpow : Int → (M →*' G) → (M →*' G) := fun n f => { toFun := fun x => f x ^ n, map_mul' := sorry }
    ∀ (n : Nat) (a : M →*' G), zpow (Int.ofNat (Nat.succ n)) a = a * zpow (Int.ofNat n) a := by
  simp only [Int.ofNat_eq_coe] -- commenting out this line makes simp loop
  simp (config := { failIfUnchanged := false }) only [mul_comm] -- should not produce: unexpected bound variable 2
  sorry

theorem ex₂ {M} [Mul M] [Mul G] [Pow G Int] :
    let zpow : Int → (M →*' G) → (M →*' G) := fun n f => { toFun := fun x => f x ^ n, map_mul' := sorry }
    ∀ (n : Nat) (a : M →*' G), zpow (Int.ofNat (Nat.succ n)) a = a * zpow (Int.ofNat n) a := by
  simp only [mul_comm]
  sorry

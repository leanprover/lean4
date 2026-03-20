import Lean
/-! # cbv_simproc for Nat.fib using fast doubling

This test demonstrates a cbv_simproc ported from Mathlib's `norm_num` extension that evaluates `Nat.fib.
-/

open Lean Meta Sym.Simp

-- Define fib
def Nat.fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => Nat.fib n + Nat.fib (n + 1)

theorem Nat.fib_zero : Nat.fib 0 = 0 := rfl
theorem Nat.fib_one : Nat.fib 1 = 1 := rfl
theorem Nat.fib_two : Nat.fib 2 = 1 := rfl

def IsFibAux (n a b : Nat) := Nat.fib n = a ∧ Nat.fib (n + 1) = b

theorem isFibAux_zero : IsFibAux 0 0 1 :=
  ⟨Nat.fib_zero, Nat.fib_one⟩

theorem isFibAux_one : IsFibAux 1 1 1 :=
  ⟨Nat.fib_one, Nat.fib_two⟩

theorem fib_add_two {n : Nat} : Nat.fib (n + 2) = Nat.fib n + Nat.fib (n + 1) := by grind [Nat.fib]

theorem fib_add (m n : Nat) : Nat.fib (m + n + 1) = Nat.fib m * Nat.fib n + Nat.fib (m + 1) * Nat.fib (n + 1) := by
  induction n generalizing m with
  | zero => grind [Nat.fib]
  | succ n ih =>
    specialize ih (m + 1)
    rw [Nat.add_assoc m 1 n, Nat.add_comm 1 n] at ih
    simp only [fib_add_two, ih]
    grind

theorem fib_two_mul (n : Nat) : Nat.fib (2 * n) = Nat.fib n * (2 * Nat.fib (n + 1) - Nat.fib n) := by
  cases n
  · simp [Nat.fib]
  · rw [Nat.two_mul, ← Nat.add_assoc, fib_add, fib_add_two, Nat.two_mul]
    have add_tsub_cancel_right : ∀ (a b : Nat), a + b - b = a := by grind
    simp only [← Nat.add_assoc, add_tsub_cancel_right]
    grind

theorem fib_two_mul_add_one (n : Nat) : Nat.fib (2 * n + 1) = Nat.fib (n + 1) ^ 2 + Nat.fib n ^ 2 := by
  rw [Nat.two_mul, fib_add]
  grind [Nat.two_mul, fib_add]

theorem isFibAux_two_mul {n a b n' a' b' : Nat} (H : IsFibAux n a b)
    (hn : 2 * n = n') (h1 : a * (2 * b - a) = a') (h2 : a * a + b * b = b') :
    IsFibAux n' a' b' :=
  ⟨by rw [← hn, fib_two_mul, H.1, H.2, ← h1],
   by rw [← hn, fib_two_mul_add_one, H.1, H.2, Nat.pow_two, Nat.pow_two, Nat.add_comm, h2]⟩

theorem fib_two_mul_add_two (n : Nat) :
    Nat.fib (2 * n + 2) = Nat.fib (n + 1) * (2 * Nat.fib n + Nat.fib (n + 1)) := by
  rw [fib_add_two, fib_two_mul, fib_two_mul_add_one]
  induction n <;> grind [Nat.fib]

theorem isFibAux_two_mul_add_one {n a b n' a' b' : Nat} (H : IsFibAux n a b)
    (hn : 2 * n + 1 = n') (h1 : a * a + b * b = a') (h2 : b * (2 * a + b) = b') :
    IsFibAux n' a' b' :=
  ⟨by rw [← hn, fib_two_mul_add_one, H.1, H.2, Nat.pow_two, Nat.pow_two, Nat.add_comm, h1],
   by rw [← hn, fib_two_mul_add_two, H.1, H.2, h2]⟩

theorem isFibAux_two_mul_done {n a b n' a' : Nat} (H : IsFibAux n a b)
    (hn : 2 * n = n') (h : a * (2 * b - a) = a') : Nat.fib n' = a' :=
  (isFibAux_two_mul H hn h rfl).1

theorem isFibAux_two_mul_add_one_done {n a b n' a' : Nat} (H : IsFibAux n a b)
    (hn : 2 * n + 1 = n') (h : a * a + b * b = a') : Nat.fib n' = a' :=
  (isFibAux_two_mul_add_one H hn h rfl).1

namespace FibSimproc

partial def proveNatFibAux (n : Nat) : Nat × Nat × Expr :=
  match n with
  | 0 => ⟨0, 1, mkConst ``isFibAux_zero⟩
  | 1 => ⟨1, 1, mkConst ``isFibAux_one⟩
  | n =>
    let half := n / 2
    let ⟨a, b, H⟩ := proveNatFibAux half
    let en := mkNatLit half
    let ea := mkNatLit a
    let eb := mkNatLit b
    if n % 2 == 0 then
      let a' := a * (2 * b - a)
      let b' := a * a + b * b
      let en' := mkNatLit n
      let ea' := mkNatLit a'
      let eb' := mkNatLit b'
      let hn := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Nat) en'
      let h1 := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Nat) ea'
      let h2 := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Nat) eb'
      let proof := mkAppN (mkConst ``isFibAux_two_mul) #[en, ea, eb, en', ea', eb', H, hn, h1, h2]
      ⟨a', b', proof⟩
    else
      let a' := a * a + b * b
      let b' := b * (2 * a + b)
      let en' := mkNatLit n
      let ea' := mkNatLit a'
      let eb' := mkNatLit b'
      let hn := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Nat) en'
      let h1 := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Nat) ea'
      let h2 := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Nat) eb'
      let proof := mkAppN (mkConst ``isFibAux_two_mul_add_one) #[en, ea, eb, en', ea', eb', H, hn, h1, h2]
      ⟨a', b', proof⟩

def proveNatFib (n : Nat) : Nat × Expr :=
  match n with
  | 0 => ⟨0, mkConst ``Nat.fib_zero⟩
  | 1 => ⟨1, mkConst ``Nat.fib_one⟩
  | 2 => ⟨1, mkConst ``Nat.fib_two⟩
  | n =>
    let half := n / 2
    let ⟨a, b, H⟩ := proveNatFibAux half
    let en := mkNatLit half
    let ea := mkNatLit a
    let eb := mkNatLit b
    if n % 2 == 0 then
      let result := a * (2 * b - a)
      let en' := mkNatLit n
      let eresult := mkNatLit result
      let hn := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Nat) en'
      let h := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Nat) eresult
      let proof := mkAppN (mkConst ``isFibAux_two_mul_done) #[en, ea, eb, en', eresult, H, hn, h]
      ⟨result, proof⟩
    else
      let result := a * a + b * b
      let en' := mkNatLit n
      let eresult := mkNatLit result
      let hn := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Nat) en'
      let h := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Nat) eresult
      let proof := mkAppN (mkConst ``isFibAux_two_mul_add_one_done) #[en, ea, eb, en', eresult, H, hn, h]
      ⟨result, proof⟩

end FibSimproc

section
cbv_simproc cbv_eval evalFib (Nat.fib _) := fun e => do
  let_expr Nat.fib arg := e | return .rfl
  let some n := Sym.getNatValue? arg | return .rfl
  let ⟨result, proof⟩ := FibSimproc.proveNatFib n
  let resultExpr ← Sym.share (mkNatLit result)
  return .step resultExpr proof (done := true)

theorem fib_0 : Nat.fib 0 = 0 := by cbv
theorem fib_1 : Nat.fib 1 = 1 := by cbv
theorem fib_2 : Nat.fib 2 = 1 := by cbv
theorem fib_10 : Nat.fib 10 = 55 := by cbv
theorem fib_20 : Nat.fib 20 = 6765 := by cbv
theorem fib_30 : Nat.fib 30 = 832040 := by cbv
theorem fib_50 : Nat.fib 50 = 12586269025 := by cbv
theorem fib_100 : Nat.fib 100 = 354224848179261915075 := by cbv

theorem fib_sum : Nat.fib 10 + Nat.fib 20 = 6820 := by cbv

/--
info: theorem fib_sum : Nat.fib 10 + Nat.fib 20 = 6820 :=
of_eq_true
  (Eq.trans
    (congrFun'
      (congrArg Eq
        (Eq.trans
          (congr
            (congrArg HAdd.hAdd
              (isFibAux_two_mul_done
                (isFibAux_two_mul_add_one (isFibAux_two_mul isFibAux_one (Eq.refl 2) (Eq.refl 1) (Eq.refl 2))
                  (Eq.refl 5) (Eq.refl 5) (Eq.refl 8))
                (Eq.refl 10) (Eq.refl 55)))
            (isFibAux_two_mul_done
              (isFibAux_two_mul
                (isFibAux_two_mul_add_one (isFibAux_two_mul isFibAux_one (Eq.refl 2) (Eq.refl 1) (Eq.refl 2))
                  (Eq.refl 5) (Eq.refl 5) (Eq.refl 8))
                (Eq.refl 10) (Eq.refl 55) (Eq.refl 89))
              (Eq.refl 20) (Eq.refl 6765)))
          (Eq.refl 6820)))
      6820)
    (eq_self 6820))
-/
#guard_msgs in
#print fib_sum

end

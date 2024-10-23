import Std.Tactic.RSimp

/-!
This test applies the rsimp_decide tactic to a calculation from the equational_theories
project.
-/

/-
First a bit of of setup. Maybe some of this can eventually become part of the default
rsimp-set. The proofs here are not great, sorry for that, I hope they do not break too often.
-/

def Fin.all {n : Nat} (P : ∀ i < n, Bool) : Bool := go n (Nat.le_refl n)
  where
  go := Nat.rec
    (motive := fun i => i ≤ n → Bool)
    (fun _ => true)
    (fun i ih p => P i (by omega) && ih (by omega))

def Nat.all_below (n : Nat) (P : Nat → Bool) : Bool :=
  Nat.rec true (fun i ih => P i && ih) n

@[rsimp]
def Fin.all_eq_all_below {n : Nat} (P : ∀ i < n, Bool) (P' : Nat → Bool)
  (hP : ∀  i h, P i h = P' i) : Fin.all P = Nat.all_below n P' := by
  suffices ∀ i (h : i ≤ n), Fin.all.go P i h = Nat.all_below i P'
    by apply this
  intros i h
  induction i
  case zero => rfl
  case succ i ih =>
    simp [all.go, Nat.all_below]
    congr
    · apply hP
    · apply ih


theorem Bool.eq_of_eq_true_iff_eq_true {a b : Bool} : (a = true ↔ b = true) → a = b := by
  cases a; cases b
  all_goals simp

@[rsimp]
theorem Fin.decideAll_to_Fin.all {n : Nat} {P : Fin n → Prop} [DecidablePred P] :
    decide (∀ x, P x) = Fin.all (fun i h => decide (P ⟨i, h⟩)) := by
  apply Bool.eq_of_eq_true_iff_eq_true
  simp [Fin.all]
  suffices ∀ i (h : i ≤ n), (∀ j (hj : j < i), P ⟨j, by omega⟩) = all.go (fun i h ↦ decide (P ⟨i, h⟩)) i h by
    rw [← this n (Nat.le_refl n)]
    exact forall_iff
  intro i h
  induction i
  case a.zero =>
    simp [all.go]
    rfl
  case a.succ i ih =>
    apply propext
    calc (∀ (j : Nat) (hj : j < i + 1), P ⟨j, by omega⟩)
      _ ↔ P ⟨i, h⟩ ∧ (∀ (j : Nat) (hj : j < i), P ⟨j, by omega⟩) := by
        constructor
        · exact fun h' => ⟨h' i (by omega), fun j hj => h' j (by omega)⟩
        · intro h' j hj
          by_cases j = i
          · subst j; apply h'.1
          · apply h'.2 j (by omega)
      _ ↔ decide (P ⟨i, h⟩) = true ∧ (∀ (j : Nat) (hj : j < i), P ⟨j, by omega⟩) := by simp
      _ ↔ decide (P ⟨i, h⟩) = true ∧ all.go (fun i h ↦ decide (P ⟨i, h⟩)) i (by omega) = true := by rw [ih]
      _ ↔ all.go (fun i h ↦ decide (P ⟨i, h⟩)) (i+1) h = true := by simp [all.go]


@[rsimp]
theorem Nat.decideEq_to_beq {x y : Nat} :
    decide (x = y) = Nat.beq x y := by
  simp [decide, instDecidableEqNat, Nat.decEq]
  split
  · simp [*]
  · simp [*]


attribute [rsimp] Nat.decideEq_to_beq
attribute [rsimp] Fin.ext_iff
attribute [rsimp] Fin.val_mul Fin.val_add Mul.mul Fin.mul
attribute [rsimp] instHAdd instHMul instAddNat instMulNat instHPow instPowNat instNatPowNat
attribute [rsimp] instHMod Nat.instMod instHDiv Nat.instDiv

-- Now the example calculation

namespace Example
class Magma (α : Type u) where /-- op -/ op : α → α → α
@[inherit_doc] infixl:65 " ◇ " => Magma.op

def opOfTable {n : Nat} (t : Nat) (a : Fin n) (b : Fin n) : Fin n :=
  let i := a.val * n + b.val
  let r := (t / n^i) % n
  ⟨r, Nat.mod_lt _ (Fin.pos a)⟩

attribute [rsimp] Magma.op opOfTable

def table : Nat := 176572862725894008122698639442158340463570358062018791456284713065412594783123644086682432661794684073102303331486778326370940525772356431236683795848309863276639424307474540043134479302998

abbrev Equation2531 (G: Type _) [Magma G] := ∀ x y : G, x = (y ◇ ((y ◇ x) ◇ x)) ◇ y

@[rsimp]
def M2 : Magma (Fin 13) where
  op := opOfTable table

-- #time approx 130ms
theorem Equation2531_M2_unopt : @Equation2531 (Fin 13) M2 := by decide

set_option trace.tactic.rsimp_decide true
set_option pp.fieldNotation.generalized false

/--
info: [tactic.rsimp_decide] Optimized expression:
      Nat.all_below 13 fun i =>
        Nat.all_below 13 fun i_1 =>
          Nat.beq i
            (Nat.mod
              (Nat.div Example.table
                (Nat.pow 13
                  (Nat.add
                    (Nat.mul
                      (Nat.mod
                        (Nat.div Example.table
                          (Nat.pow 13
                            (Nat.add (Nat.mul i_1 13)
                              (Nat.mod
                                (Nat.div Example.table
                                  (Nat.pow 13
                                    (Nat.add
                                      (Nat.mul
                                        (Nat.mod (Nat.div Example.table (Nat.pow 13 (Nat.add (Nat.mul i_1 13) i))) 13)
                                        13)
                                      i)))
                                13))))
                        13)
                      13)
                    i_1)))
              13)
-/
#guard_msgs in
-- #time -- approx 33ms
theorem Equation2531_M2_opt : @Equation2531 (Fin 13) M2 := by rsimp_decide

end Example

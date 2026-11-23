import Std.Tactic.BVDecide
/-
source: TPTP v9.3.1 GRA120-1 (CNF_UNS), epr_experiment/tptp_epr/CNF_UNS/GRA120-1.p
translated by the tptp_epr driver of bv_epr 0.13.0 (-Dtrace.tptp_epr=true)
bv_epr 0.13.0: Unsatisfiable in 2.42 s
-/

theorem TPTP_GRA120_1
    : ∀ {α : Type} [αNonempty : Nonempty α] (r : α → α → Prop) (v0 v1 v2 v3 v4 v5 v6 v7 v8 : α),
      (∀ (X Y : α), ¬ r X Y ∨ r Y X)
        → (∀ (Z X Y : α), X = Y ∨ X = Z ∨ Y = Z ∨ ¬ r X Y ∨ ¬ r X Z ∨ ¬ r Y Z)
        → (∀ (Z X Y W : α),
          X = Y ∨ X = Z ∨ Y = Z ∨ X = W ∨ Y = W ∨ Z = W ∨ r X Y ∨ r X Z ∨ r Y Z ∨ r X W ∨ r Y W
            ∨ r Z W)
        → v0 ≠ v1 → v0 ≠ v2 → v1 ≠ v2 → v0 ≠ v3 → v1 ≠ v3 → v2 ≠ v3 → v0 ≠ v4 → v1 ≠ v4 → v2 ≠ v4
        → v3 ≠ v4 → v0 ≠ v5 → v1 ≠ v5 → v2 ≠ v5 → v3 ≠ v5 → v4 ≠ v5 → v0 ≠ v6 → v1 ≠ v6 → v2 ≠ v6
        → v3 ≠ v6 → v4 ≠ v6 → v5 ≠ v6 → v0 ≠ v7 → v1 ≠ v7 → v2 ≠ v7 → v3 ≠ v7 → v4 ≠ v7 → v5 ≠ v7
        → v6 ≠ v7 → v0 ≠ v8 → v1 ≠ v8 → v2 ≠ v8 → v3 ≠ v8 → v4 ≠ v8 → v5 ≠ v8 → v6 ≠ v8 → v7 ≠ v8
        → False := by
  epr (cegarRounds := 1000)

import Std.Tactic.BVDecide

set_option trustCompiler true
/-
source: TPTP v9.3.1 MSC015-1.010 (CNF_UNS), epr_experiment/tptp_epr/CNF_UNS/MSC015-1.010.p
translated by the tptp_epr driver of bv_epr 0.13.0 (-Dtrace.tptp_epr=true)
bv_epr 0.13.0: Unsatisfiable in 11.32 s
-/

set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem TPTP_MSC015_1_010 :
  ∀ {α : Type} [αNonempty : Nonempty α] (s0 : α) (p : α → α → α → α → α → α → α → α → α → α → Prop) (s1 : α),
    p s0 s0 s0 s0 s0 s0 s0 s0 s0 s0 →
      (∀ (X7 X5 X2 X1 X3 X0 X8 X4 X6 : α), ¬p X0 X1 X2 X3 X4 X5 X6 X7 X8 s0 ∨ p X0 X1 X2 X3 X4 X5 X6 X7 X8 s1) →
        (∀ (X7 X5 X2 X1 X3 X0 X4 X6 : α), ¬p X0 X1 X2 X3 X4 X5 X6 X7 s0 s1 ∨ p X0 X1 X2 X3 X4 X5 X6 X7 s1 s0) →
          (∀ (X5 X2 X1 X3 X0 X4 X6 : α), ¬p X0 X1 X2 X3 X4 X5 X6 s0 s1 s1 ∨ p X0 X1 X2 X3 X4 X5 X6 s1 s0 s0) →
            (∀ (X5 X2 X1 X3 X0 X4 : α), ¬p X0 X1 X2 X3 X4 X5 s0 s1 s1 s1 ∨ p X0 X1 X2 X3 X4 X5 s1 s0 s0 s0) →
              (∀ (X2 X1 X3 X0 X4 : α), ¬p X0 X1 X2 X3 X4 s0 s1 s1 s1 s1 ∨ p X0 X1 X2 X3 X4 s1 s0 s0 s0 s0) →
                (∀ (X2 X1 X3 X0 : α), ¬p X0 X1 X2 X3 s0 s1 s1 s1 s1 s1 ∨ p X0 X1 X2 X3 s1 s0 s0 s0 s0 s0) →
                  (∀ (X2 X1 X0 : α), ¬p X0 X1 X2 s0 s1 s1 s1 s1 s1 s1 ∨ p X0 X1 X2 s1 s0 s0 s0 s0 s0 s0) →
                    (∀ (X1 X0 : α), ¬p X0 X1 s0 s1 s1 s1 s1 s1 s1 s1 ∨ p X0 X1 s1 s0 s0 s0 s0 s0 s0 s0) →
                      (∀ (X0 : α), ¬p X0 s0 s1 s1 s1 s1 s1 s1 s1 s1 ∨ p X0 s1 s0 s0 s0 s0 s0 s0 s0 s0) →
                        ¬p s0 s1 s1 s1 s1 s1 s1 s1 s1 s1 ∨ p s1 s0 s0 s0 s0 s0 s0 s0 s0 s0 →
                          ¬p s1 s1 s1 s1 s1 s1 s1 s1 s1 s1 → False
  := by
  epr (cegarRounds := 1000)

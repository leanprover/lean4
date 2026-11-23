import Std.Tactic.BVDecide

set_option trustCompiler true
/-
source: TPTP v9.3.1 GRP129-3.004 (CNF_UNS), epr_experiment/tptp_epr/CNF_UNS/GRP129-3.004.p
translated by the tptp_epr driver of bv_epr 0.13.0 (-Dtrace.tptp_epr=true)
bv_epr 0.13.0: Unsatisfiable in 1.27 s
-/

theorem TPTP_GRP129_3_004
    : ∀ {α : Type} [αNonempty : Nonempty α] (e_0 e_1 : α) (next : α → α → Prop) (e_2 e_3 e_4 : α)
        (greater cycle equalish : α → α → Prop) (group_element : α → Prop)
        (product : α → α → α → Prop),
      next e_0 e_1 → next e_1 e_2 → next e_2 e_3 → next e_3 e_4 → greater e_1 e_0 → greater e_2 e_0
        → greater e_3 e_0 → greater e_4 e_0 → greater e_2 e_1 → greater e_3 e_1 → greater e_4 e_1
        → greater e_3 e_2 → greater e_4 e_2 → greater e_4 e_3
        → (∀ (Z X Y : α), ¬ cycle X Y ∨ ¬ cycle X Z ∨ equalish Y Z)
        → (∀ (X : α), ¬ group_element X ∨ cycle X e_0 ∨ cycle X e_1 ∨ cycle X e_2 ∨ cycle X e_3)
        → cycle e_4 e_0
        → (∀ (Z Z1 X Y W : α),
          ¬ cycle X Y ∨ ¬ cycle W Z ∨ ¬ next X W ∨ ¬ greater Y e_0 ∨ ¬ next Z Z1 ∨ equalish Y Z1)
        → (∀ (Z1 X Y Z2 W : α),
          ¬ cycle X Z1 ∨ ¬ cycle Y e_0 ∨ ¬ cycle W Z2 ∨ ¬ next Y W ∨ ¬ greater Y X
            ∨ ¬ greater Z1 Z2)
        → (∀ (X Y : α), ¬ cycle X e_0 ∨ ¬ product X e_1 Y ∨ ¬ greater Y X)
        → (∀ (Z X X1 Y : α),
          ¬ cycle X Y ∨ ¬ product X e_1 Z ∨ ¬ greater Y e_0 ∨ ¬ next X X1 ∨ equalish Z X1)
        → group_element e_1 → group_element e_2 → group_element e_3 → group_element e_4
        → ¬ equalish e_1 e_2 → ¬ equalish e_1 e_3 → ¬ equalish e_1 e_4 → ¬ equalish e_2 e_1
        → ¬ equalish e_2 e_3 → ¬ equalish e_2 e_4 → ¬ equalish e_3 e_1 → ¬ equalish e_3 e_2
        → ¬ equalish e_3 e_4 → ¬ equalish e_4 e_1 → ¬ equalish e_4 e_2 → ¬ equalish e_4 e_3
        → (∀ (X Y : α),
          ¬ group_element X ∨ ¬ group_element Y ∨ product X Y e_1 ∨ product X Y e_2
            ∨ product X Y e_3 ∨ product X Y e_4)
        → (∀ (Z X Y W : α), ¬ product X Y W ∨ ¬ product X Y Z ∨ equalish W Z)
        → (∀ (Z X Y W : α), ¬ product X W Y ∨ ¬ product X Z Y ∨ equalish W Z)
        → (∀ (Z X Y W : α), ¬ product W Y X ∨ ¬ product Z Y X ∨ equalish W Z)
        → (∀ (Z1 X Y Z2 : α), ¬ product Y X Z1 ∨ ¬ product X Z1 Z2 ∨ product Z1 Y Z2)
        → False := by
  epr (cegarRounds := 1000)

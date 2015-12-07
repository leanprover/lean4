-- Testing all possible cases of [unit_action]
set_option blast.strategy "unit"

universes l1 l2
variables {A B C : Prop}
variables {X : Type.{l1}} {Y : Type.{l2}}
variables {P : Y → Prop}

-- Types as antecedents
example (H : X → A) (x : X) : A := by blast
example (H : X → A → B) (x : X) (nb : ¬ B) : ¬ A := by blast
example (H : A → X → B → C) (x : X) (a : A) (nc : ¬ C) : ¬ B := by blast

-- Universally quantified facts
example (H : A → X → B → ∀ y : Y, P y) (x : X) (a : A) (nc : ¬ ∀ y : Y, P y) : ¬ B := by blast
example (H : A → X → B → ¬ ∀ y : Y, P y) (x : X) (a : A) (nc : ∀ y : Y, P y) : ¬ B := by blast

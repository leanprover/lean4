/-
   1. A ∧ B → C ==> { A → B → C }
   2. A ∨ B → C ==> { A → C, B → C }
   3. A → B ∧ C ==> { A → C, A → C }
   4. A ↔ B ==> { (A → B) ∧ (B → A) }
   5. Push negations inside ∧ and ∨ (when using classical)
   6. ite A B C ==> { A → B, ¬ A → C }
-/

open simplifier.unit_simp
set_option simplify.max_steps 100000

namespace vars
variables {A B C D E F G : Prop}
variables [A_dec : decidable A]

#simplify iff env 0 A → B ∧ C
#simplify iff env 0 A → B ∧ C ∧ D
#simplify iff env 0 A → B ∧ C → D
#simplify iff env 0 A → B ∧ C → D ∧ E
#simplify iff env 0 A → B ∧ C → D ∨ E → F ∧ G
#simplify iff env 0 A → B ∧ C → D ∨ E → ((F → G) ∧ (G → F))

end vars

namespace cs

constants {A B C D E F G : Prop}
constants [A_dec : decidable A]

attribute A_dec [instance]

#simplify iff env 0 ite A B C
#simplify iff env 0 ite A B C → B ∧ C
#simplify iff env 0 A → (ite A B C)
#simplify iff env 0 A → B ∧ (ite A B C) → D ∨ E → ((F → G) ∧ (G → F))
end cs

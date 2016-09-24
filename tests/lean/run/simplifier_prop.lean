open tactic

meta definition psimp : tactic unit :=
do simp_lemmas  ← mk_simp_lemmas_core reducible [] [`congr],
   (new_target, Heq) ← target >>= simplify_core failed `eq simp_lemmas,
   assert `Htarget new_target, swap,
   Ht ← get_local `Htarget,
   mk_app `eq.mpr [Heq, Ht] >>= exact,
   triv

variables (P Q R S : Prop)

-- Iff
example : P = P := by psimp

-- Pi
example : P → true := by psimp
example : ∀ (X : Type), X → true := by psimp

-- Eq
example : (P = P) = true := by psimp
example : ((¬ P) = (¬ Q)) = (P = Q) := by psimp
example : (true = P) = P := by psimp
example : (false = P) = ¬ P := by psimp
example : (false = ¬ P) = P := by psimp
example : (P = true) = P := by psimp
example : (P = false) = ¬ P := by psimp
example : (¬ P = false) = P := by psimp
example : (P = ¬ P) = false := by psimp
example : (¬ P = P) = false := by psimp

-- Not
example : ¬ ¬ P = P := by psimp
example : ¬ ¬ ¬ P = ¬ P := by psimp
example : ¬ false = true := by psimp
example : ¬ true = false := by psimp

example : (¬ (P = Q)) = ((¬ P) = Q) := by psimp

-- Ite
namespace ite
variable [P_dec : decidable P]
include P_dec

example : ite true P Q = P := by psimp
example : ite false P Q = Q := by psimp
example : ite P Q Q = Q := by psimp

-- Classical
--example : ite (not P) Q R = ite P R Q := by psimp

-- Instances
example : ite P (ite P Q R) S = ite P Q S := by psimp
example : ite P S (ite P Q R) = ite P S R := by psimp
example : ite P (ite P S (ite P Q R)) S = ite P S S := by psimp
end ite

-- And
example : (P ∧ P) = P := by psimp
example : (P ∧ P) = (P ∧ P ∧ P) := by psimp

example : (P ∧ Q) = (Q ∧ P) := by psimp
example : (P ∧ Q ∧ R) = (R ∧ Q ∧ P) := by psimp
example : (P ∧ Q ∧ R ∧ P ∧ Q ∧ R) = (R ∧ Q ∧ P) := by psimp

example : (P ∧ true) = P := by psimp
example : (true ∧ P ∧ true ∧ P ∧ true) = P := by psimp

example : (P ∧ false) = false := by psimp
example : (false ∧ P ∧ false ∧ P ∧ false) = false := by psimp

example : (P ∧ Q ∧ R ∧ true ∧ ¬ P) = false := by psimp

-- Or
example : (P ∨ P) = P := by psimp
example : (P ∨ P) = (P ∨ P ∨ P) := by psimp

example : (P ∨ Q) = (Q ∨ P) := by psimp
example : (P ∨ Q ∨ R) = (R ∨ Q ∨ P) := by psimp
example : (P ∨ Q ∨ R ∨ P ∨ Q ∨ R) = (R ∨ Q ∨ P) := by psimp

example : (P ∨ false) = P := by psimp
example : (false ∨ P ∨ false ∨ P ∨ false) = P := by psimp

example : (P ∨ true) = true := by psimp
example : (true ∨ P ∨ true ∨ P ∨ true) = true := by psimp

example : (P ∨ Q ∨ R ∨ false ∨ ¬ P) = true := by psimp

-- Contextual
example : (P = Q) → (P = Q) := by psimp
example : (P = Q) → ((P ∧ P) = (Q ∧ Q)) := by psimp
example : (P = (Q ∧ R)) → ((P ∧ P) = (R ∧ P ∧ Q)) := by psimp
example : (P = (Q ∧ R ∧ Q)) → ((P ∧ P) = (R ∧ P ∧ Q)) := by psimp
example : (P = (Q ∧ R)) → ((¬ Q ∧ P ∧ ¬ R) = false) := by psimp

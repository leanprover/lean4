import tools.super.cdcl

example {a} : a → ¬a → false := by cdcl
example {a} : a ∨ ¬a := by cdcl
example {a b} : a → (a → b) → b := by cdcl
example {a b c} : (a → b) → (¬a → b) → (b → c) → b ∧ c := by cdcl

open tactic

private meta def lit_unification : tactic unit :=
do ls ← local_context, first $ do l ← ls, [do apply l, assumption]

example {p : ℕ → Prop} : p 2 ∨ p 4 → (p (2*2) → p (2+0)) → p (1+1) :=
by cdcl_t lit_unification

example {p : ℕ → Prop} :
        list.foldl (λf v, f ∧ (v ∨ ¬v)) true (p <$> list.range 5) :=
begin (target >>= whnf >>= change), cdcl end

example {a b c : Prop} : (a → b) → (b → c) → (a → c) := by cdcl

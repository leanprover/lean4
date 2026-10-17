/-!
The `grind` normalizer rewrites `∀ _ : α, True` to `True` for every `α`, not only for
propositions. Such antecedents arise when the body of a quantified hypothesis simplifies away,
e.g. the condition `∀ t, x = abs (abs t) → False` of an equation theorem instantiated with
`x := app M N`. Before, `(∀ _ : α, True) → q` was left as an implication with an opaque
antecedent that nothing could establish, and `q` was lost. Reported in leanprover/cslib#1141.
-/

example (α : Type) (q : Prop) (h : (∀ _ : α, True) → q) : (∀ _ : α, True) → q := by
  grind_norm check
  guard_target =ₛ q
  exact h fun _ => trivial

inductive Term where
  | bvar : Nat → Term
  | fvar : String → Term
  | abs  : Term → Term
  | app  : Term → Term → Term

namespace Term

inductive LC : Term → Prop
  | fvar (x : String) : LC (fvar x)
  | abs (e : Term) : LC (abs e)
  | app {l r} : LC l → LC r → LC (app l r)

attribute [grind .] LC.fvar LC.app

@[grind]
inductive IsFvar : Term → Prop
  | fvar (m : String) : IsFvar (fvar m)

@[grind]
inductive ClosedUnderApp (P : Term → Prop) : Term → Prop where
  | base {a} : P a → ClosedUnderApp P a
  | app {a b} : ClosedUnderApp P a → ClosedUnderApp P b → ClosedUnderApp P (app a b)

@[grind →]
theorem closedunderapp_lc {Q} {M : Term} (h : ∀ x, Q x → LC x) (h2 : ClosedUnderApp Q M) :
    LC M := by
  induction h2 with grind

def two_vars_are_enough : Term → Bool
  | bvar n => n < 2
  | fvar _ => false
  | abs (abs t) => two_vars_are_enough t
  | app t1 t2 => two_vars_are_enough t1 && two_vars_are_enough t2
  | _ => false

def abs_two_vars_are_enough : Term → Bool
  | abs (abs t) => two_vars_are_enough t
  | _ => false

/-
The equations as plain `[grind =]` theorems. The equation theorems of a function defined in
another module get the same treatment: their conditions are not recognized as `match` conditions.
-/
@[grind =] theorem abs_two_vars_are_enough_abs_abs (t : Term) :
    abs_two_vars_are_enough (abs (abs t)) = two_vars_are_enough t := rfl
@[grind =] theorem abs_two_vars_are_enough_eq_false (x : Term)
    (h : ∀ t, x = abs (abs t) → False) : abs_two_vars_are_enough x = false := by
  unfold abs_two_vars_are_enough; split <;> grind

@[grind ←]
theorem abs_two_vars_are_enough_lc {t} (h : abs_two_vars_are_enough t) : LC t := by
  unfold abs_two_vars_are_enough at h
  split at h
  · exact .abs _
  · simp at h

@[grind]
def fvar_or_combinator (a : Term) : Prop := IsFvar a ∨ abs_two_vars_are_enough a

/-- `HeadReduction2_preserver_fvar_or_combinator`, `appL` case, in leanprover/cslib#1141. -/
example (M1 M2 N : Term)
    (a_ih : ClosedUnderApp fvar_or_combinator M1 → ClosedUnderApp fvar_or_combinator M2)
    (hm : ClosedUnderApp fvar_or_combinator (app M1 N)) :
    ClosedUnderApp fvar_or_combinator (app M2 N) := by
  grind

end Term

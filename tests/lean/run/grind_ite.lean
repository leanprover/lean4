import Std

/-!
# If normalization

Rustan Leino, Stephan Merz, and Natarajan Shankar have recently been discussing challenge problems
to compare proof assistants.
(See https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Rustan's.20challenge)

Their first suggestion was "if-normalization".

Here we state the problem in the Lean,
and then construct a clean solution where all verification work is done by `grind`.

(This solution builds upon an earlier solution by Chris Hughes, which had less automation
but made use of the powerful termination checker.)
-/

/-- An if-expression is either boolean literal, a numbered variable,
or an if-then-else expression where each subexpression is an if-expression. -/
inductive IfExpr
  | lit : Bool → IfExpr
  | var : Nat → IfExpr
  | ite : IfExpr → IfExpr → IfExpr → IfExpr
deriving DecidableEq

namespace IfExpr

/--
An if-expression has a "nested if" if it contains
an if-then-else where the "if" is itself an if-then-else.
-/
def hasNestedIf : IfExpr → Bool
  | lit _ => false
  | var _ => false
  | ite (ite _ _ _) _ _ => true
  | ite _ t e => t.hasNestedIf || e.hasNestedIf

/--
An if-expression has a "constant if" if it contains
an if-then-else where the "if" is itself a literal.
-/
def hasConstantIf : IfExpr → Bool
  | lit _ => false
  | var _ => false
  | ite (lit _) _ _ => true
  | ite i t e => i.hasConstantIf || t.hasConstantIf || e.hasConstantIf

/--
An if-expression has a "redundant if" if it contains
an if-then-else where the "then" and "else" clauses are identical.
-/
def hasRedundantIf : IfExpr → Bool
  | lit _ => false
  | var _ => false
  | ite i t e => t == e || i.hasRedundantIf || t.hasRedundantIf || e.hasRedundantIf

/--
All the variables appearing in an if-expressions, read left to right, without removing duplicates.
-/
def vars : IfExpr → List Nat
  | lit _ => []
  | var i => [i]
  | ite i t e => i.vars ++ t.vars ++ e.vars

/--
A helper function to specify that two lists are disjoint.
-/
def _root_.List.disjoint {α} [DecidableEq α] : List α → List α → Bool
  | [], _ => true
  | x::xs, ys => x ∉ ys && xs.disjoint ys

/--
An if expression evaluates each variable at most once if for each if-then-else
the variables in the "if" clause are disjoint from the variables in the "then" clause, and
the variables in the "if" clause are disjoint from the variables in the "else" clause.
-/
def disjoint : IfExpr → Bool
  | lit _ => true
  | var _ => true
  | ite i t e =>
      i.vars.disjoint t.vars && i.vars.disjoint e.vars && i.disjoint && t.disjoint && e.disjoint

/--
An if expression is "normalized" if it has no nested, constant, or redundant ifs,
and it evaluates each variable at most once.
-/
def normalized (e : IfExpr) : Bool :=
  !e.hasNestedIf && !e.hasConstantIf && !e.hasRedundantIf && e.disjoint

/--
The evaluation of an if expression at some assignment of variables.
-/
def eval (f : Nat → Bool) : IfExpr → Bool
  | lit b => b
  | var i => f i
  | ite i t e => bif i.eval f then t.eval f else e.eval f

end IfExpr

/--
This is the statement of the if normalization problem.

We require a function that transforms if expressions to normalized if expressions,
preserving all evaluations.
-/
def IfNormalization : Type := { Z : IfExpr → IfExpr // ∀ e, (Z e).normalized ∧ (Z e).eval = e.eval }

/-!
# A solution to the if normalization challenge in Lean, using `grind`.
-/

-- `grind` is currently experimental, but for now we can suppress the warnings about this.
namespace IfExpr

/--
Custom size function for if-expressions, used for proving termination.
It is designed so that if we decrease the size of the "if" condition by one,
we are allowed to increase the size of the branches by one, and still be smaller.
-/
-- We add the `simp` attribute so the termination checker can unfold the function.
@[simp] def normSize : IfExpr → Nat
  | lit _ => 0
  | var _ => 1
  | .ite i t e => 2 * normSize i + max (normSize t) (normSize e) + 1

-- TODO: `grind` canonicalizer is spending a lot of time unfolding the following function.
-- TODO: remove after the new module system will hide this declaration.
seal Std.DHashMap.insert
seal Std.TreeMap.insert

def normalize (assign : Std.HashMap Nat Bool) : IfExpr → IfExpr
  | lit b => lit b
  | var v =>
    match assign[v]? with
    | none => var v
    | some b => lit b
  | ite (lit true)  t _ => normalize assign t
  | ite (lit false) _ e => normalize assign e
  | ite (ite a b c) t e => normalize assign (ite a (ite b t e) (ite c t e))
  | ite (var v)     t e =>
    match assign[v]? with
    | none =>
      let t' := normalize (assign.insert v true) t
      let e' := normalize (assign.insert v false) e
      if t' = e' then t' else ite (var v) t' e'
    | some b => normalize assign (ite (lit b) t e)
  termination_by e => e.normSize

-- We tell `grind` to unfold our definitions above.
attribute [local grind] normalized hasNestedIf hasConstantIf hasRedundantIf disjoint vars eval List.disjoint

theorem normalize_spec (assign : Std.HashMap Nat Bool) (e : IfExpr) :
    (normalize assign e).normalized
    ∧ (∀ f, (normalize assign e).eval f = e.eval fun w => assign[w]?.getD (f w))
    ∧ ∀ (v : Nat), v ∈ vars (normalize assign e) → ¬ v ∈ assign := by
  fun_induction normalize with grind

-- We can also prove other variations, where we spell "`v` is not in `assign`"
-- different ways, and `grind` doesn't mind.

example (assign : Std.HashMap Nat Bool) (e : IfExpr) :
    (normalize assign e).normalized
    ∧ (∀ f, (normalize assign e).eval f = e.eval fun w => assign[w]?.getD (f w))
    ∧ ∀ (v : Nat), v ∈ vars (normalize assign e) → assign.contains v = false := by
  fun_induction normalize with grind

example (assign : Std.HashMap Nat Bool) (e : IfExpr) :
    (normalize assign e).normalized
    ∧ (∀ f, (normalize assign e).eval f = e.eval fun w => assign[w]?.getD (f w))
    ∧ ∀ (v : Nat), v ∈ vars (normalize assign e) → assign[v]? = none := by
  fun_induction normalize with grind

/--
We recall the statement of the if-normalization problem.

We want a function from if-expressions to if-expressions,
that outputs normalized if-expressions and preserves meaning.
-/
example : IfNormalization :=
  ⟨_, fun e => ⟨(IfExpr.normalize_spec ∅ e).1, by simp [(IfExpr.normalize_spec ∅ e).2.1]⟩⟩

-- Finally, just to show off, we check that we can replace `HashMap` with `TreeMap`
-- without needing to touch any proofs:

def normalize' (assign : Std.TreeMap Nat Bool) : IfExpr → IfExpr
  | lit b => lit b
  | var v =>
    match assign[v]? with
    | none => var v
    | some b => lit b
  | ite (lit true)  t _ => normalize' assign t
  | ite (lit false) _ e => normalize' assign e
  | ite (ite a b c) t e => normalize' assign (ite a (ite b t e) (ite c t e))
  | ite (var v)     t e =>
    match assign[v]? with
    | none =>
      let t' := normalize' (assign.insert v true) t
      let e' := normalize' (assign.insert v false) e
      if t' = e' then t' else ite (var v) t' e'
    | some b => normalize' assign (ite (lit b) t e)
  termination_by e => e.normSize

theorem normalize'_spec (assign : Std.TreeMap Nat Bool) (e : IfExpr) :
    (normalize' assign e).normalized
    ∧ (∀ f, (normalize' assign e).eval f = e.eval fun w => assign[w]?.getD (f w))
    ∧ ∀ (v : Nat), v ∈ vars (normalize' assign e) → ¬ v ∈ assign := by
  fun_induction normalize' with grind

example (assign : Std.TreeMap Nat Bool) (e : IfExpr) :
    (normalize' assign e).normalized
    ∧ (∀ f, (normalize' assign e).eval f = e.eval fun w => assign[w]?.getD (f w))
    ∧ ∀ (v : Nat), v ∈ vars (normalize' assign e) → assign.contains v = false := by
  fun_induction normalize' with grind

example (assign : Std.TreeMap Nat Bool) (e : IfExpr) :
    (normalize' assign e).normalized
    ∧ (∀ f, (normalize' assign e).eval f = e.eval fun w => assign[w]?.getD (f w))
    ∧ ∀ (v : Nat), v ∈ vars (normalize' assign e) → assign[v]? = none := by
  fun_induction normalize' with grind

end IfExpr

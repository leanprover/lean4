import Std.Data.HashMap.Lemmas

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
deriving DecidableEq, Repr

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
@[grind] def _root_.List.disjoint {α} [DecidableEq α] : List α → List α → Bool
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
set_option grind.warning false

-- We first set up some convenient macros for dealing with subtypes using `grind`.

/-- Construct a term of a subtype, using `grind` to discharge the condition. -/
macro "g⟨" a:term "⟩" : term => `(⟨$a, by grind (gen := 8) (splits := 9)⟩)
/--
Replace a term of a subtype with a term of a different subtype, using the same data,
and using `grind` to discharge the new condition (with access to the old condition).
-/
macro "c⟨" a:term "⟩" : term => `(have aux := $a; ⟨aux.1, by grind⟩)



namespace IfExpr

attribute [grind] List.mem_cons List.not_mem_nil List.mem_append
  Option.getD_some Option.getD_none

attribute [local grind] normalized hasNestedIf hasConstantIf hasRedundantIf disjoint vars

-- I'd prefer to use `TreeMap` here, but its `getElem?_insert` lemma is not useful.
attribute [grind] Std.HashMap.getElem?_insert

/-!
Lemmas for `eval`.
-/
@[grind] theorem eval_lit : (lit b).eval f = b := rfl
@[grind] theorem eval_var : (var i).eval f = f i := rfl
@[grind] theorem eval_ite_lit :
    (ite (.lit b) t e).eval f = bif b then t.eval f else e.eval f := rfl
@[grind] theorem eval_ite_var :
    (ite (.var i) t e).eval f = bif f i then t.eval f else e.eval f := rfl
@[grind] theorem eval_ite_ite {a b c d e : IfExpr} :
    (ite (ite a b c) d e).eval f = (ite a (ite b d e) (ite c d e)).eval f := by grind [eval]

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

set_option profiler true
/--
Normalizes the expression at the same time as
making the variable assignments to literal booleans given by `assign`.
-/
def normalize (assign : Std.HashMap Nat Bool) :
    (e : IfExpr) → { e' : IfExpr //
        -- The result is normalized
        e'.normalized
        -- Evaluating the result is the same as evaluating the original expression, overriding the values with `assign`
        ∧ (∀ f, e'.eval f = e.eval fun w => assign[w]?.getD (f w))
        -- There are no remaining variables from `assign` in the result
        ∧ ∀ (v : Nat), v ∈ vars e' → assign[v]? = none } -- TODO: replace the conclusion with `v ∉ assign`
  | lit b => g⟨lit b⟩
  | var v =>
    match h : assign[v]? with
    | none => g⟨var v⟩
    | some b => g⟨lit b⟩
  | ite (lit true)  t e => c⟨normalize assign t⟩
  | ite (lit false) t e => c⟨normalize assign e⟩
  | ite (ite a b c) t e => c⟨normalize assign (ite a (ite b t e) (ite c t e))⟩
  | ite (var v)     t e =>
    match h : assign[v]? with
    | none =>
      have ⟨t', _⟩ := normalize (assign.insert v true) t
      have ⟨e', _⟩ := normalize (assign.insert v false) e
      g⟨if t' = e' then t' else ite (var v) t' e'⟩
    | some b => c⟨normalize assign (ite (lit b) t e)⟩
  termination_by e => e.normSize

/-
We recall the statement of the if-normalization problem.

We want a function from if-expressions to if-expressions,
that outputs normalized if-expressions and preserves meaning.
-/
example : IfNormalization :=
  ⟨_, fun e => ⟨(IfExpr.normalize ∅ e).2.1, by simp [(IfExpr.normalize ∅ e).2.2.1]⟩⟩

end IfExpr

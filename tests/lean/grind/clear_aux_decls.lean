section Mathlib.Data.List.Sigma

universe u v

namespace List

variable {α : Type u} {β : α → Type v} {l : List (Sigma β)}

/-- List of keys from a list of key-value pairs -/
def keys : List (Sigma β) → List α :=
  map Sigma.fst

/-- Determines whether the store uses a key several times. -/
def NodupKeys (l : List (Sigma β)) : Prop :=
  l.keys.Nodup

variable [DecidableEq α]

/-! ### `dlookup` -/

/-- `dlookup a l` is the first value in `l` corresponding to the key `a`,
  or `none` if no such element exists. -/
def dlookup (a : α) : List (Sigma β) → Option (β a)
  | [] => none
  | ⟨a', b⟩ :: l => if h : a' = a then some (Eq.recOn h b) else dlookup a l

/-- Remove the first pair with the key `a`. -/
def kerase (a : α) : List (Sigma β) → List (Sigma β) :=
  eraseP fun s => a = s.1

/-- Insert the pair `⟨a, b⟩` and erase the first pair with the key `a`. -/
def kinsert (a : α) (b : β a) (l : List (Sigma β)) : List (Sigma β) :=
  ⟨a, b⟩ :: kerase a l

end List

end Mathlib.Data.List.Sigma

section Mathlib.Data.List.AList

universe u v

open List

variable {α : Type u} {β : α → Type v}

structure AList (β : α → Type v) : Type max u v where
  entries : List (Sigma β)
  nodupKeys : entries.NodupKeys

namespace AList

/-- The empty association list. -/
instance : EmptyCollection (AList β) :=
  ⟨⟨[], sorry⟩⟩

variable [DecidableEq α]

/-- Look up the value associated to a key in an association list. -/
def lookup (a : α) (s : AList β) : Option (β a) :=
  s.entries.dlookup a

@[simp]
theorem lookup_empty (a) : lookup a (∅ : AList β) = none :=
  rfl

/-- Insert a key-value pair into an association list and erase any existing pair
  with the same key. -/
def insert (a : α) (b : β a) (s : AList β) : AList β :=
  ⟨kinsert a b s.entries, sorry⟩

theorem lookup_insert {a a' : α} {β} {b : β a} (s : AList β) :
    (s.insert a b).lookup a' = if h : a' = a then some (h ▸ b) else s.lookup a' := by
  sorry

end AList

end Mathlib.Data.List.AList


/-!
# If normalization

Rustan Leino, Stephan Merz, and Natarajan Shankar have recently been discussing challenge problems
to compare proof assistants.
(See https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Rustan's.20challenge)

Their first suggestion was "if-normalization".

This file contains a Lean formulation of the problem. See `Result.lean` for a Lean solution.
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
an if-then-else where the then and else clauses are identical.
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
the variables in the if clause are disjoint from the variables in the then clause, and
the variables in the if clause are disjoint from the variables in the else clause.
-/
def disjoint : IfExpr → Bool
  | lit _ => true
  | var _ => true
  | ite i t e =>
      i.vars.disjoint t.vars && i.vars.disjoint e.vars && i.disjoint && t.disjoint && e.disjoint

/--
An if expression is "normalized" if it has not nested, constant, or redundant ifs,
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

We require a function from that transforms if expressions to normalized if expressions,
preserving all evaluations.
-/
def IfNormalization : Type := { Z : IfExpr → IfExpr // ∀ e, (Z e).normalized ∧ (Z e).eval = e.eval }


/-!
# A solution to the if normalization challenge in Lean.

See `Statement.lean` for background.
-/

macro "◾" : tactic => `(tactic| grind)
macro "◾" : term => `(term| by grind)

set_option grind.warning false

namespace IfExpr

attribute [grind] Subtype
grind_pattern Subtype.property => self.val

attribute [grind] List.mem_cons List.not_mem_nil List.mem_append Option.elim_none Option.elim_some
  id

attribute [grind] List.disjoint

attribute [grind] AList.lookup_insert
attribute [grind] List.cons_append List.nil_append

attribute [local grind] normalized hasNestedIf hasConstantIf hasRedundantIf disjoint vars

variable {b : Bool} {f : Nat → Bool} {i : Nat} {t e : IfExpr}

/-!
Simp lemmas for `eval`.
We don't want a `simp` lemma for `(ite i t e).eval` in general, only once we know the shape of `i`.
-/
@[simp, grind] theorem eval_lit : (lit b).eval f = b := rfl
@[simp, grind] theorem eval_var : (var i).eval f = f i := rfl
@[simp, grind] theorem eval_ite_lit :
    (ite (.lit b) t e).eval f = bif b then t.eval f else e.eval f := rfl
@[simp, grind] theorem eval_ite_var :
    (ite (.var i) t e).eval f = bif f i then t.eval f else e.eval f := rfl
@[simp, grind] theorem eval_ite_ite {a b c d e : IfExpr} :
    (ite (ite a b c) d e).eval f = (ite a (ite b d e) (ite c d e)).eval f := by grind [eval]

/-- Custom size function for if-expressions, used for proving termination. -/
@[simp] def normSize : IfExpr → Nat
  | lit _ => 0
  | var _ => 1
  | .ite i t e => 2 * normSize i + max (normSize t) (normSize e) + 1

/-- Normalizes the expression at the same time as assigning all variables in
`e` to the literal booleans given by `l` -/
def normalize (l : AList (fun _ : Nat => Bool)) :
    (e : IfExpr) → { e' : IfExpr //
        (∀ f, e'.eval f = e.eval (fun w => (l.lookup w).elim (f w) id))
        ∧ e'.normalized
        ∧ ∀ (v : Nat), v ∈ vars e' → l.lookup v = none }
  | lit b => ⟨lit b, ◾⟩
  | var v =>
    match h : l.lookup v with
    | none => ⟨var v, ◾⟩
    | some b => ⟨lit b, ◾⟩
  | .ite (lit true)   t e =>
    -- Fails with `tactic 'grind.clear_aux_decls' failed`:
    ⟨(normalize l t).1, ◾⟩
    -- Workaround:
    -- have t' := normalize l t; ⟨t'.1, ◾⟩
  | .ite (lit false)  t e => have e' := normalize l e; ⟨e'.1, ◾⟩
  | .ite (.ite a b c) t e => have i' := normalize l (.ite a (.ite b t e) (.ite c t e)); ⟨i'.1, ◾⟩
  | .ite (var v)      t e =>
    match h : l.lookup v with
    | none =>
      have ⟨t', ht₁, ht₂, ht₃⟩ := normalize (l.insert v true) t
      have ⟨e', he₁, he₂, he₃⟩ := normalize (l.insert v false) e
      ⟨if t' = e' then t' else .ite (var v) t' e', by
        refine ⟨fun f => ?_, ?_, fun w b => ?_⟩
        · -- eval = eval
          simp only [apply_ite, eval_ite_var]
          cases hfv : f v
          · simp_all
            congr
            ◾
          · simp [h, ht₁]
            congr
            ◾
        · -- normalized
          split
          · ◾
          · simp only [normalized, disjoint]
            ◾
        · -- lookup = none
          ◾⟩
    | some b =>
      have i' := normalize l (.ite (lit b) t e); ⟨i'.1, ◾⟩
  termination_by e => e.normSize

/-
We recall the statement of the if-normalization problem.

We want a function from if-expressions to if-expressions,
that outputs normalized if-expressions and preserves meaning.
-/
example : IfNormalization :=
  ⟨_, fun e => ⟨(IfExpr.normalize ∅ e).2.2.1, by simp [(IfExpr.normalize ∅ e).2.1]⟩⟩

end IfExpr

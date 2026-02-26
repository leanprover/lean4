module
public import Std.Data.HashMap
public import Std.Data.TreeMap

inductive IfExpr
  | lit : Bool → IfExpr
  | var : Nat → IfExpr
  | ite : IfExpr → IfExpr → IfExpr → IfExpr
deriving DecidableEq

namespace IfExpr

def hasNestedIf : IfExpr → Bool
  | lit _ => false
  | var _ => false
  | ite (ite _ _ _) _ _ => true
  | ite _ t e => t.hasNestedIf || e.hasNestedIf

def hasConstantIf : IfExpr → Bool
  | lit _ => false
  | var _ => false
  | ite (lit _) _ _ => true
  | ite i t e => i.hasConstantIf || t.hasConstantIf || e.hasConstantIf

def hasRedundantIf : IfExpr → Bool
  | lit _ => false
  | var _ => false
  | ite i t e => t == e || i.hasRedundantIf || t.hasRedundantIf || e.hasRedundantIf

def vars : IfExpr → List Nat
  | lit _ => []
  | var i => [i]
  | ite i t e => i.vars ++ t.vars ++ e.vars

def _root_.List.disjoint {α} [DecidableEq α] : List α → List α → Bool
  | [], _ => true
  | x::xs, ys => x ∉ ys && xs.disjoint ys

def disjoint : IfExpr → Bool
  | lit _ => true
  | var _ => true
  | ite i t e =>
      i.vars.disjoint t.vars && i.vars.disjoint e.vars && i.disjoint && t.disjoint && e.disjoint

def normalized (e : IfExpr) : Bool :=
  !e.hasNestedIf && !e.hasConstantIf && !e.hasRedundantIf && e.disjoint

def eval (f : Nat → Bool) : IfExpr → Bool
  | lit b => b
  | var i => f i
  | ite i t e => bif i.eval f then t.eval f else e.eval f

end IfExpr

def IfNormalization : Type := { Z : IfExpr → IfExpr // ∀ e, (Z e).normalized ∧ (Z e).eval = e.eval }

namespace IfExpr

@[simp] def normSize : IfExpr → Nat
  | lit _ => 0
  | var _ => 1
  | .ite i t e => 2 * normSize i + max (normSize t) (normSize e) + 1

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
  fun_induction normalize
  next => grind => finish?
  next => grind => finish?
  next => grind => finish?
  next => grind => finish?
  next => grind => finish?
  next => grind => finish?
  next => grind => finish?
  next => grind => finish?
  next => grind => finish?

example (assign : Std.HashMap Nat Bool) (e : IfExpr) :
    (normalize assign e).normalized
    ∧ (∀ f, (normalize assign e).eval f = e.eval fun w => assign[w]?.getD (f w))
    ∧ ∀ (v : Nat), v ∈ vars (normalize assign e) → assign.contains v = false := by
  fun_induction normalize
  next => grind => finish?
  next => grind => finish?
  next => grind => finish?
  next => grind => finish?
  next => grind => finish?
  next => grind => finish?
  next => grind => finish?
  next => grind => finish?
  next => grind => finish?

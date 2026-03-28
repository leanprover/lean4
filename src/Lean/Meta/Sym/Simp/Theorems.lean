/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Sym.Pattern
public import Lean.Meta.DiscrTree
import Lean.Meta.Sym.Simp.DiscrTree
import Lean.Meta.AppBuilder
import Lean.ExtraModUses
import Init.Omega
public section
namespace Lean.Meta.Sym.Simp

/--
A simplification theorem for the structural simplifier.

Contains both the theorem expression and a precomputed pattern for efficient unification
during rewriting.
-/
structure Theorem where
  /-- The theorem expression, typically `Expr.const declName` for a named theorem. -/
  expr    : Expr
  /-- Precomputed pattern extracted from the theorem's type for efficient matching. -/
  pattern : Pattern
  /-- Right-hand side of the equation. -/
  rhs     : Expr
  /-- If `true`, the theorem is a permutation rule (e.g., `x + y = y + x`).
  Rewriting is only applied when the result is strictly less than the input
  (using `acLt`), preventing infinite loops. -/
  perm    : Bool := false
  deriving Inhabited

instance : BEq Theorem where
  beq thm₁ thm₂ := thm₁.expr == thm₂.expr

/-- Collection of simplification theorems available to the simplifier. -/
structure Theorems where
  thms : DiscrTree Theorem := {}
  deriving Inhabited

def Theorems.insert (thms : Theorems) (thm : Theorem) : Theorems :=
  { thms with thms := insertPattern thms.thms thm.pattern thm }

def Theorems.getMatch (thms : Theorems) (e : Expr) : Array Theorem :=
  Sym.getMatch thms.thms e

def Theorems.getMatchWithExtra (thms : Theorems) (e : Expr) : Array (Theorem × Nat) :=
  Sym.getMatchWithExtra thms.thms e

/--
Check whether `lhs` and `rhs` (with `numVars` pattern variables represented as `.bvar` indices
`≥ 0` before any binder entry) are permutations of each other — same structure with only
pattern variable indices rearranged via a consistent bijection.

Bvars with index `< offset` are "local" (introduced by binders inside the pattern) and must
match exactly. Bvars with index `≥ offset` are pattern variables and may be permuted,
but the mapping must be a bijection.

Simplified compared to `Meta.simp`'s `isPerm`:
- Uses de Bruijn indices instead of metavariables
- No `.proj` (folded into applications) or `.letE` (zeta-expanded) cases
-/
private abbrev IsPermM := ReaderT Nat $ StateT (Array (Option Nat)) $ Except Unit

private partial def isPermAux (a b : Expr) : IsPermM Unit := do
  match a, b with
  | .bvar i, .bvar j =>
    let offset ← read
    if i < offset && j < offset then
      unless i == j do throw ()
    else if i >= offset && j >= offset then
      let pi := i - offset
      let pj := j - offset
      let fwd ← get
      if h : pi >= fwd.size then throw () else
      match fwd[pi] with
      | none =>
        -- Check injectivity: pj must not already be a target of another mapping
        if fwd.contains (some pj) then throw ()
        set (fwd.set pi (some pj))
      | some pj' => unless pj == pj' do throw ()
    else throw ()
  | .app f₁ a₁, .app f₂ a₂ => isPermAux f₁ f₂; isPermAux a₁ a₂
  | .mdata _ s, t => isPermAux s t
  | s, .mdata _ t => isPermAux s t
  | .forallE _ d₁ b₁ _, .forallE _ d₂ b₂ _ => isPermAux d₁ d₂; withReader (· + 1) (isPermAux b₁ b₂)
  | .lam _ d₁ b₁ _, .lam _ d₂ b₂ _ => isPermAux d₁ d₂; withReader (· + 1) (isPermAux b₁ b₂)
  | s, t => unless s == t do throw ()

def isPerm (numVars : Nat) (lhs rhs : Expr) : Bool :=
  ((isPermAux lhs rhs).run 0 |>.run (Array.replicate numVars none)) matches .ok _

/-- Describes how a theorem's conclusion was adapted to an equality for use in `Sym.simp`. -/
private inductive EqAdaptation where
  /-- Already an equality `lhs = rhs`. Proof is used as-is. -/
  | eq
  /-- Was `¬ p`. Proof `h` adapted to `eq_false h : p = False`. -/
  | eqFalse
  /-- Was `p ↔ q`. Proof `h` adapted to `propext h : p = q`. -/
  | iff
  /-- Was a proposition `p`. Proof `h` adapted to `eq_true h : p = True`. -/
  | eqTrue

/--
Analyze the conclusion of a theorem type and extract `(lhs, rhs)` for use as a
rewrite rule in `Sym.simp`. Handles:
- `lhs = rhs` — used as-is
- `¬ p` — adapted to `p = False`
- `p ↔ q` — adapted to `p = q`
- `p` (proposition) — adapted to `p = True`
-/
private def selectEqKey (type : Expr) : MetaM (Expr × Expr × EqAdaptation) := do
  match_expr type with
  | Eq _ lhs rhs => return (lhs, rhs, .eq)
  | Not p => return (p, mkConst ``False, .eqFalse)
  | Iff lhs rhs => return (lhs, rhs, .iff)
  | _ =>
    unless (← isProp type) do
      throwError "cannot use as a simp theorem, conclusion is not a proposition{indentExpr type}"
    return (type, mkConst ``True, .eqTrue)

/--
Wrap a proof expression according to the adaptation applied to its type.
Given a proof `h : <original type>`, returns a proof of the adapted equality.
This wrapping must be applied AFTER the proof has been applied to its quantified arguments.
-/
private def wrapProof (numVars : Nat) (expr : Expr) (adaptation : EqAdaptation) : MetaM Expr :=
  match adaptation with
  | .eq => return expr
  | .eqFalse =>
    wrapInner numVars expr fun h => mkAppM ``eq_false #[h]
  | .iff =>
    wrapInner numVars expr fun h => mkAppM ``propext #[h]
  | .eqTrue =>
    wrapInner numVars expr fun h => mkAppM ``eq_true #[h]
where
  /-- Wraps the innermost application of `expr` (after `numVars` arguments) with `wrap`. -/
  wrapInner (numVars : Nat) (expr : Expr) (wrap : Expr → MetaM Expr) : MetaM Expr := do
    let type ← inferType expr
    forallBoundedTelescope type numVars fun xs _ => do
      let h := mkAppN expr xs
      mkLambdaFVars xs (← wrap h)

def mkTheoremFromDecl (declName : Name) : MetaM Theorem := do
  let (pattern, (rhs, adaptation)) ← mkPatternFromDeclWithKey declName selectEqKey
  let expr ← wrapProof pattern.varTypes.size (mkConst declName) adaptation
  let perm := isPerm pattern.varTypes.size pattern.pattern rhs
  return { expr, pattern, rhs, perm }

/-- Create a `Theorem` from a proof expression. Handles equalities, `¬`, `↔`, and propositions. -/
def mkTheoremFromExpr (e : Expr) : MetaM Theorem := do
  let (pattern, (rhs, adaptation)) ← mkPatternFromExprWithKey e [] selectEqKey
  let expr ← wrapProof pattern.varTypes.size e adaptation
  let perm := isPerm pattern.varTypes.size pattern.pattern rhs
  return { expr, pattern, rhs, perm }

/--
Environment extension storing a set of `Sym.Simp` theorems.
Each named set gets its own extension, created by `registerSymSimpAttr`.
-/
abbrev SymSimpExtension := SimpleScopedEnvExtension Theorem Theorems

def SymSimpExtension.getTheorems (ext : SymSimpExtension) : CoreM Theorems :=
  return ext.getState (← getEnv)

def mkSymSimpExt (name : Name := by exact decl_name%) : IO SymSimpExtension :=
  registerSimpleScopedEnvExtension {
    name     := name
    initial  := {}
    addEntry := fun thms thm => thms.insert thm
    exportEntry? := fun lvl thm => do
      let .const declName _ := thm.expr | return thm
      guard (lvl == .private || !isPrivateName declName)
      return thm
  }

abbrev SymSimpExtensionMap := Std.HashMap Name SymSimpExtension

builtin_initialize symSimpExtensionMapRef : IO.Ref SymSimpExtensionMap ← IO.mkRef {}

def getSymSimpExtension? (attrName : Name) : CoreM (Option SymSimpExtension) := do
  let ext? := (← symSimpExtensionMapRef.get)[attrName]?
  if let some ext := ext? then
    recordExtraModUseFromDecl (isMeta := true) ext.ext.name
  return ext?

end Lean.Meta.Sym.Simp

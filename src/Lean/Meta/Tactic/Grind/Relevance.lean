/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Tactic.Grind.Types
import Init.Grind.Util
public section
namespace Lean.Meta.Grind

/-!
Relevance filter for `grind` facts, see `Grind.Config.filterFacts`.

A fact is split into the atoms of its propositional skeleton. It is relevant if an atom is
processed by an active solver (`Solvers.isRelevantAtom`), is a `Bool` equality, contains a symbol
of an active E-matching theorem, or occurs in a relevant fact. A skipped fact is asserted as soon
as one of its atoms occurs in a relevant fact. The facts are not normalized yet, so the checks
work on their input form (e.g., `a ≥ b` and `a ≠ b`).
-/

/--
Returns the type of the arguments of `e` if it is an equality or an arithmetic relation.
Returns `none` if the type contains loose bound variables.
-/
def getRelationType? (e : Expr) : Option Expr :=
  let α? := match_expr e with
    | Eq α _ _ => some α
    | Ne α _ _ => some α
    | LE.le α _ _ _ => some α
    | LT.lt α _ _ _ => some α
    | GE.ge α _ _ _ => some α
    | GT.gt α _ _ _ => some α
    | Dvd.dvd α _ _ _ => some α
    | Nat.le _ _ => some (mkConst ``Nat)
    | Nat.lt _ _ => some (mkConst ``Nat)
    | _ => none
  α?.filter (!·.hasLooseBVars)

/-- Returns `true` if `e` is an equality or an arithmetic relation over a type satisfying `p`. -/
@[inline] def isRelationOver (e : Expr) (p : Expr → GoalM Bool) : GoalM Bool := do
  let some α := getRelationType? e | return false
  p α

namespace Relevance

/--
Collects the atoms of the propositional skeleton of `e`. Atoms under binders may contain loose
bound variables. If `quant := false`, a universally quantified proposition is an atom.
-/
partial def collectAtoms (e : Expr) (quant : Bool) (atoms : Array Expr := #[]) : Array Expr :=
  match e with
  | .mdata _ e => collectAtoms e quant atoms
  | .forallE _ d b _ =>
    if !b.hasLooseBVars then
      -- Implication. The domain is a proposition since `e` is a fact.
      collectAtoms b quant (collectAtoms d quant atoms)
    else if quant then
      collectAtoms b quant atoms
    else
      atoms.push e
  | .letE _ _ v b _ => collectAtoms b quant (collectAtoms v quant atoms)
  | .const ``True _ | .const ``False _ => atoms
  | _ =>
    match_expr e with
    | Lean.Grind.alreadyNorm p => collectAtoms p quant atoms
    | Lean.Grind.MatchCond p => collectAtoms p quant atoms
    | Not p => collectAtoms p quant atoms
    | And p q => collectAtoms q quant (collectAtoms p quant atoms)
    | Or p q => collectAtoms q quant (collectAtoms p quant atoms)
    | Iff p q => collectAtoms q quant (collectAtoms p quant atoms)
    | Exists _ p =>
      if let .lam _ _ b _ := p then collectAtoms b quant atoms else atoms.push e
    | ite α c _ a b =>
      if α.isProp then
        collectAtoms b quant (collectAtoms a quant (collectAtoms c quant atoms))
      else
        atoms.push e
    | _ =>
      if e.isAppOfArity ``Eq 3 && e.appFn!.appFn!.appArg!.isProp then
        collectAtoms e.appArg! quant (collectAtoms e.appFn!.appArg! quant atoms)
      else
        atoms.push e

private def isBoolEq (e : Expr) : Bool :=
  e.isAppOfArity ``Eq 3 && e.appFn!.appFn!.appArg!.isConstOf ``Bool

private def containsRelevantSymbol (e : Expr) : GoalM Bool := do
  let symbols := (← readThe Context).relevantSymbols
  if symbols.isEmpty then return false
  return Option.isSome <| e.find? fun
    | .const declName _ => symbols.contains declName
    | _ => false

def isRelevantAtom (e : Expr) : GoalM Bool := do
  if isBoolEq e then return true
  if (← Solvers.isRelevantAtom e) then return true
  containsRelevantSymbol e

/-- Returns the free variables that are sides of the equality `e`. -/
private def getEqFVarSides (e : Expr) : Array Expr :=
  let_expr Eq _ lhs rhs := e | #[]
  (if lhs.isFVar then #[lhs] else #[]) ++ (if rhs.isFVar then #[rhs] else #[])

/--
Keys of a skipped fact with the given atoms: an equality whose side is a free variable `x` becomes
relevant when `x` occurs in a relevant fact, e.g., `b = ⟨x + 1, d⟩` and `b.n ≠ 8`.
-/
def getSkippedKeys (atoms : Array Expr) : Array Expr :=
  atoms.foldl (init := #[]) fun keys atom =>
    if atom.hasLooseBVars then keys else keys.push atom ++ getEqFVarSides atom

/-- Keys of a relevant fact with the given atoms: the atoms and the free variables occurring in them. -/
def getRelevantKeys (atoms : Array Expr) : Array Expr :=
  let fvars := atoms.foldl (init := {}) fun s atom => collectFVars s atom
  let keys := atoms.filter (!·.hasLooseBVars)
  fvars.fvarIds.foldl (init := keys) fun keys fvarId => keys.push (mkFVar fvarId)

/--
Returns `(relevant, atoms)` where `atoms` are the atoms of the propositional skeleton of `prop`.
The relevance checks stop at the first relevant atom.
-/
def checkFact (prop : Expr) : GoalM (Bool × Array Expr) := do
  let config ← getConfig
  let atoms := collectAtoms prop (quant := config.ematch > 0 && config.genLocal > 0)
  -- A fact without atoms (e.g., `¬True`) is trivial to process.
  if atoms.isEmpty then return (true, atoms)
  let known := (← get).relevance.keys
  if (getSkippedKeys atoms).any known.contains then return (true, atoms)
  for atom in atoms do
    if (← isRelevantAtom atom) then return (true, atoms)
  return (false, atoms)

/-- Adds `keys` to the keys of relevant facts, and asserts the skipped facts sharing a new key. -/
partial def registerKeys (keys : Array Expr) (generation : Nat := 0) : GoalM Unit := do
  let s := (← get).relevance
  let newKeys := keys.filter (!s.keys.contains ·)
  if newKeys.isEmpty then return ()
  let known := newKeys.foldl (init := s.keys) fun known key => known.insert key
  modify fun s => { s with relevance.keys := known }
  if s.skipped.isEmpty then return ()
  let (woken, skipped) := s.skipped.partition fun fact => fact.keys.any newKeys.contains
  if woken.isEmpty then return ()
  modify fun s => { s with relevance.skipped := skipped }
  -- `skipped` is in reverse order.
  for fact in woken.reverse do
    trace[grind.relevance] "asserting skipped fact{indentExpr fact.prop}"
    addNewRawFact fact.proof fact.prop (max generation fact.generation) .input .other
    registerKeys (getRelevantKeys fact.atoms) generation

end Relevance

/--
Returns `none` if `prop` must be processed, and registers its keys. Otherwise, `prop` is
irrelevant for the active solvers, and its atoms are returned. See `Grind.Config.filterFacts`.
-/
def checkIrrelevant? (prop : Expr) (generation : Nat := 0) : GoalM (Option (Array Expr)) := do
  unless (← readThe Context).filterFacts do return none
  let (relevant, atoms) ← Relevance.checkFact (← instantiateMVars prop)
  if relevant then
    Relevance.registerKeys (Relevance.getRelevantKeys atoms) generation
    return none
  else
    return some atoms

/--
Records an irrelevant fact with the given atoms (see `checkIrrelevant?`). It is asserted when it
becomes relevant.
-/
def skipFact (proof prop : Expr) (atoms : Array Expr) (generation : Nat := 0) : GoalM Unit := do
  trace[grind.relevance] "skipping{indentExpr prop}"
  let keys := Relevance.getSkippedKeys atoms
  modify fun s => { s with relevance.skipped := { proof, prop, generation, atoms, keys } :: s.relevance.skipped }

/--
Returns `true` if the fact `prop` with proof `proof` must be processed. Otherwise, it is skipped.
See `checkIrrelevant?`.
-/
def filterFact (prop proof : Expr) (generation : Nat := 0) : GoalM Bool := do
  let some atoms ← checkIrrelevant? prop generation | return true
  skipFact proof prop atoms generation
  return false

/-- Registers the keys of a fact that is asserted without filtering. See `filterFact`. -/
def registerRelevantFact (prop : Expr) (generation : Nat) : GoalM Unit := do
  unless (← readThe Context).filterFacts do return ()
  let prop ← instantiateMVars prop
  let config ← getConfig
  let atoms := Relevance.collectAtoms prop (quant := config.ematch > 0 && config.genLocal > 0)
  Relevance.registerKeys (Relevance.getRelevantKeys atoms) generation

builtin_initialize registerTraceClass `grind.relevance

end Lean.Meta.Grind

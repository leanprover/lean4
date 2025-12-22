/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Expr
public import Lean.Data.PersistentHashMap
public import Lean.Meta.Tactic.Grind.Theorems
public section
namespace Lean.Meta.Grind

/-- Types that `grind` will case-split on. -/
structure CasesTypes where
  casesMap : PHashMap Name Bool := {}
  deriving Inhabited

def CasesTypes.insert (s : CasesTypes) (declName : Name) (eager : Bool) : CasesTypes :=
  { s with casesMap := s.casesMap.insert declName eager }

abbrev ExtTheorems := PHashSet Name

structure SymbolPriorities where
  map : PHashMap Name Nat := {}
  deriving Inhabited

/-- Inserts `declName ↦ prio` into `s`. -/
def SymbolPriorities.insert (s : SymbolPriorities) (declName : Name) (prio : Nat) : SymbolPriorities :=
  { s with map := s.map.insert declName prio }

inductive EMatchTheoremKind where
  | eqLhs (gen : Bool)
  | eqRhs (gen : Bool)
  | eqBoth (gen : Bool)
  | eqBwd
  | fwd
  | bwd (gen : Bool)
  | leftRight
  | rightLeft
  | default (gen : Bool)
  | user /- pattern specified using `grind_pattern` command -/
  deriving Inhabited, BEq, Repr, Hashable

structure CnstrRHS where
  /-- Abstracted universe level param names in the `rhs` -/
  levelNames : Array Name
  /-- Number of abstracted metavariable in the `rhs` -/
  numMVars   : Nat
  /-- The actual `rhs`. -/
  expr       : Expr
  deriving Inhabited, BEq, Repr

/--
Grind patterns may have constraints associated with them.
-/
inductive EMatchTheoremConstraint where
  | /--
    A constraint of the form `lhs =/= rhs`.
    The `lhs` is one of the bound variables, and the `rhs` an abstract term that must not be definitionally
    equal to a term `t` assigned to `lhs`. -/
    notDefEq  (lhs : Nat) (rhs : CnstrRHS)
  | /--
    A constraint of the form `lhs =?= rhs`.
    The `lhs` is one of the bound variables, and the `rhs` an abstract term that must be definitionally
    equal to a term `t` assigned to `lhs`. -/
    defEq  (lhs : Nat) (rhs : CnstrRHS)
  | /--
    A constraint of the form `size lhs < n`. The `lhs` is one of the bound variables.
    The size is computed ignoring implicit terms, but sharing is not taken into account.
    -/
    sizeLt (lhs : Nat) (n : Nat)
  | /--
    A constraint of the form `depth lhs < n`. The `lhs` is one of the bound variables.
    The depth is computed in constant time using the `approxDepth` field attached to expressions.
    -/
    depthLt (lhs : Nat) (n : Nat)
  | /--
    Instantiates the theorem only if its generation is less than `n`
    -/
    genLt (n : Nat)
  | /--
    Constraints of the form `is_ground x`. Instantiates the theorem only if
    `x` is ground term.
    -/
    isGround (bvarIdx : Nat)
  | /--
    Constraints of the form `is_value x` and `is_strict_value x`.
    A value is defined as
    - A constructor fully applied to value arguments.
    - A literal: numerals, strings, etc.
    - A lambda. In the strict case, lambdas are not considered.
    -/
    isValue (bvarIdx : Nat) (strict : Bool)
  | /--
    Instantiates the theorem only if less than `n` instances have been generated for this theorem.
    -/
    maxInsts (n : Nat)
  | /--
    It instructs `grind` to postpone the instantiation of the theorem until `e` is known to be `true`.
    -/
    guard (e : Expr)
  | /--
    Similar to `guard`, but checks whether `e` is implied by asserting `¬e`.
    -/
    check (e : Expr)
  | /--
    Constraints of the form `not_value x` and `not_strict_value x`.
    They are the negations of `is_value x` and `is_strict_value x`.
    -/
    notValue (bvarIdx : Nat) (strict : Bool)
  deriving Inhabited, Repr, BEq

/-- A theorem for heuristic instantiation based on E-matching. -/
structure EMatchTheorem where
  /--
  It stores universe parameter names for universe polymorphic proofs.
  Recall that it is non-empty only when we elaborate an expression provided by the user.
  When `proof` is just a constant, we can use the universe parameter names stored in the declaration.
  -/
  levelParams  : Array Name
  proof        : Expr
  numParams    : Nat
  patterns     : List Expr
  /-- Contains all symbols used in `patterns`. -/
  symbols      : List HeadIndex
  origin       : Origin
  /-- The `kind` is used for generating the `patterns`. We save it here to implement `grind?`. -/
  kind         : EMatchTheoremKind
  /-- Stores whether patterns were inferred using the minimal indexable subexpression condition. -/
  minIndexable : Bool
  cnstrs       : List EMatchTheoremConstraint := []
  deriving Inhabited

instance : TheoremLike EMatchTheorem where
  getSymbols thm := thm.symbols
  setSymbols thm symbols := { thm with symbols }
  getOrigin thm := thm.origin
  getProof thm := thm.proof
  getLevelParams thm := thm.levelParams

/-- A theorem marked with `@[grind inj]` -/
structure InjectiveTheorem where
  levelParams  : Array Name
  proof        : Expr
  /-- Contains all symbols used in the term `f` at the theorem's conclusion: `Function.Injective f`. -/
  symbols      : List HeadIndex
  origin       : Origin
  deriving Inhabited

instance : TheoremLike InjectiveTheorem where
  getSymbols thm := thm.symbols
  setSymbols thm symbols := { thm with symbols }
  getOrigin thm := thm.origin
  getProof thm := thm.proof
  getLevelParams thm := thm.levelParams

inductive Entry where
  | ext (declName : Name)
  | funCC (declName : Name)
  | cases (declName : Name) (eager : Bool)
  | ematch (thm : EMatchTheorem)
  | inj (thm : InjectiveTheorem)
  deriving Inhabited

/-
**Note**: We currently have a single normalization and symbol priority sets for all `grind` attributes.
Reason: the E-match patterns must be normalized with respect to them. If we are using multiple
`grind` attributes, they patterns would have to be re-normalized using the union of all normalizers.

Alternative design: allow a single `grind` attribute per `grind` call. Cons: when creating a new
`grind` attribute users would have to carefully setup the normalizer to ensure all `grind` assumptions
are met. Cons: users would not be able to write `grind only [attr_1, attr_2]`.
-/

structure ExtensionState where
  casesTypes : CasesTypes := {}
  extThms    : ExtTheorems := {}
  funCC      : NameSet := {}
  ematch     : Theorems EMatchTheorem := {}
  inj        : Theorems InjectiveTheorem := {}
  deriving Inhabited

abbrev Extension := SimpleScopedEnvExtension Entry ExtensionState

def ExtensionState.addEntry (s : ExtensionState) (e : Entry) : ExtensionState :=
  match e with
  | .cases declName eager => { s with casesTypes := s.casesTypes.insert declName eager }
  | .ext declName => { s with extThms := s.extThms.insert declName }
  | .funCC declName => { s with funCC := s.funCC.insert declName }
  | .ematch thm => { s with ematch := s.ematch.insert thm }
  | .inj thm => { s with inj := s.inj.insert thm }

def mkExtension (name : Name := by exact decl_name%) : IO Extension :=
  registerSimpleScopedEnvExtension {
    name     := name
    initial  := {}
    addEntry := ExtensionState.addEntry
    exportEntry? := fun lvl e => do
      -- export only annotations on public decls
      let declName := match e with
        | .inj thm | .ematch thm =>
          match thm.origin with
          | .decl declName => declName
          | _ => unreachable!
        | .ext declName | .cases declName _ | .funCC declName => declName
      guard (lvl == .private || !isPrivateName declName)
      return e
  }

/--
`grind` is parametrized by a collection of `ExtensionState`. The motivation is to allow
users to use multiple extensions simultaneously without merging them into a single structure.
The collection is scanned linearly. In practice, we expect the array to be very small.
-/
abbrev ExtensionStateArray := Array ExtensionState

def throwNotMarkedWithGrindAttribute (declName : Name) : CoreM α :=
  throwError "`{.ofConstName declName}` is not marked with the `[grind]` attribute"

end Lean.Meta.Grind

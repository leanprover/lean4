/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.HeadIndex
public import Lean.Meta.Basic
import Lean.Meta.Eqns
public section
namespace Lean.Meta.Grind
/-!
A collection of theorems. We use it to implement E-matching and injectivity theorems used by `grind`.
-/

inductive Origin where
  /-- A global declaration in the environment. -/
  | decl (declName : Name)
  /-- A local hypothesis. -/
  | fvar (fvarId : FVarId)
  /--
  A proof term provided directly to a call to `grind` where `ref`
  is the provided grind argument. The `id` is a unique identifier for the call.
  -/
  | stx (id : Name) (ref : Syntax)
  /-- It is local, but we don't have a local hypothesis for it. -/
  | local (id : Name)
  deriving Inhabited, Repr

/-- A unique identifier corresponding to the origin. -/
def Origin.key : Origin → Name
  | .decl declName => declName
  | .fvar fvarId   => fvarId.name
  | .stx id _      => id
  | .local id      => id

def Origin.pp (o : Origin) : MessageData :=
  match o with
  | .decl declName => MessageData.ofConstName declName
  | .fvar fvarId   => mkFVar fvarId
  | .stx _ ref     => ref
  | .local id      => id

instance : BEq Origin where
  beq a b := a.key == b.key

instance : Hashable Origin where
  hash a := hash a.key

structure Theorems (α : Type) where
  /-- The key is a symbol from `EMatchTheorem.symbols`. -/
  private smap : PHashMap Name (List α) := {}
  /-- Set of theorem ids that have been inserted using `insert`. -/
  private origins : PHashSet Origin := {}
  /-- Theorems that have been marked as erased -/
  private erased  : PHashSet Origin := {}
  /-- Mapping from origin to E-matching theorems associated with this origin. -/
  private omap : PHashMap Origin (List α) := {}
  deriving Inhabited

class TheoremLike (α : Type) where
  getSymbols : α → List HeadIndex
  setSymbols : α → List HeadIndex → α
  getOrigin : α → Origin
  getProof : α → Expr
  getLevelParams : α → Array Name

open TheoremLike

/--
Inserts a `thm` with symbols `[s_1, ..., s_n]` to `s`.
We add `s_1 -> { thm with symbols := [s_2, ..., s_n] }`.
When `grind` internalizes a term containing symbol `s`, we
process all theorems `thm` associated with key `s`.
If their `thm.symbols` is empty, we say they are activated.
Otherwise, we reinsert into `map`.
-/
def Theorems.insert [TheoremLike α] (s : Theorems α) (thm : α) : Theorems α := Id.run do
  let .const declName :: syms := getSymbols thm
    | unreachable!
  let thm := setSymbols thm syms
  let { smap, origins, erased, omap } := s
  let origin := getOrigin thm
  let origins := origins.insert origin
  let erased := erased.erase origin
  let smap := if let some thms := smap.find? declName then
    smap.insert declName (thm::thms)
  else
    smap.insert declName [thm]
  let omap := if let some thms := omap.find? origin then
    omap.insert origin (thm::thms)
  else
    omap.insert origin [thm]
  return { smap, origins, erased, omap }

/-- Returns `true` if `s` contains a theorem with the given origin. -/
def Theorems.contains (s : Theorems α) (origin : Origin) : Bool :=
  s.origins.contains origin

/-- Marks the theorem with the given origin as `erased` -/
def Theorems.erase (s : Theorems α) (origin : Origin) : Theorems α :=
  { s with erased := s.erased.insert origin, origins := s.origins.erase origin }

/-- Returns `true` if the theorem has been marked as erased. -/
def Theorems.isErased (s : Theorems α) (origin : Origin) : Bool :=
  s.erased.contains origin

/--
Retrieves theorems from `s` associated with the given symbol. See `Theorems.insert`.
The theorems are removed from `s`.
-/
@[inline]
def Theorems.retrieve? (s : Theorems α) (sym : Name) : Option (List α × Theorems α) :=
  if let some thms := s.smap.find? sym then
    some (thms, { s with smap := s.smap.erase sym })
  else
    none

/--
Returns theorems associated with the given origin.
-/
def Theorems.find (s : Theorems α) (origin : Origin) : List α :=
  if let some thms := s.omap.find? origin then
    thms
  else
    []

def getProofWithFreshMVarLevels [TheoremLike α] (thm : α) : MetaM Expr := do
  let proof := getProof thm
  let us := getLevelParams thm
  if proof.isConst && us.isEmpty then
    let declName := proof.constName!
    let info ← getConstVal declName
    if info.levelParams.isEmpty then
      return proof
    else
      mkConstWithFreshMVarLevels declName
  else if us.isEmpty then
    return proof
  else
    let us' ← us.mapM fun _ => mkFreshLevelMVar
    return proof.instantiateLevelParamsArray us us'

def Theorems.eraseDecl (s : Theorems α) (declName : Name) : MetaM (Theorems α) := do
  let throwErr {α} : MetaM α :=
    throwError "`{.ofConstName declName}` is not marked with the `[grind]` attribute"
  if !wasOriginallyTheorem (← getEnv) declName then
    if let some eqns ← getEqnsFor? declName then
       unless eqns.all fun eqn => s.contains (.decl eqn) do
         throwErr
       return eqns.foldl (init := s) fun s eqn => s.erase (.decl eqn)
    else
      throwErr
  else
    unless s.contains (.decl declName) do
      throwErr
    return s.erase <| .decl declName

def Theorems.getOrigins (s : Theorems α) : List Origin :=
  s.origins.toList

def Theorems.mkEmpty (α : Type) : Theorems α := {}

instance : EmptyCollection (Theorems α) where
  emptyCollection := Theorems.mkEmpty α

def getProofForDecl (declName : Name) : MetaM Expr := do
  let info ← getConstVal declName
  -- For theorems, `isProp` has already been checked at declaration time
  unless wasOriginallyTheorem (← getEnv) declName do
    unless (← isProp info.type) do
      throwError "invalid `grind` theorem `{.ofConstName declName}`, type is not a proposition"
  let us := info.levelParams.map mkLevelParam
  return mkConst declName us

/--
A `TheoremsArray α` is a collection of `Theorems α`.
The array is scanned linear during theorem activation.
This avoids the need for efficiently merging the `Theorems α` data structure.
-/
abbrev TheoremsArray (α : Type) := Array (Theorems α)

@[specialize]
def TheoremsArray.retrieve? (s : TheoremsArray α) (sym : Name) : Option (List α × TheoremsArray α) := Id.run do
  for h : i in *...s.size do
    if let some (thms, a) ← s[i].retrieve? sym then
      return some (thms, s.set i a)
  return none

def TheoremsArray.insert [TheoremLike α] (s : TheoremsArray α) (thm : α) : TheoremsArray α := Id.run do
  if s.isEmpty then
    let thms := { : Theorems α}
    #[thms.insert thm]
  else
    s.modify 0 (·.insert thm)

def TheoremsArray.isErased (s : TheoremsArray α) (origin : Origin) : Bool :=
  s.any fun thms => thms.erased.contains origin

def TheoremsArray.find (s : TheoremsArray α) (origin : Origin) : List α := Id.run do
  let mut r := []
  for h : i in *...s.size do
    let thms := s[i].find origin
    unless thms.isEmpty do
      r := r ++ thms
  return r

end Lean.Meta.Grind

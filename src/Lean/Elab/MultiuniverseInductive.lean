/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

prelude
public import Lean.Meta.Constructions
public import Lean.Meta.SizeOf
import Lean.Meta.Constructions.CtorIdx
import Lean.Meta.Constructions.CtorElim
import Lean.Meta.IndPredBelow
import Lean.Meta.Injective

public section

/-!
# Lowering a universe-heterogeneous mutual inductive block

Lean requires every member of a mutual inductive block to live in the same
universe.  The restriction is checked three times over: once while the headers
are elaborated, once after the constructors are, and once by the kernel.  So a
block like

```
mutual
inductive A : Prop where
  | fromB : B → A
  | fromC : C → A
inductive B : Type 0 where
  | fromA : Nat → A → B
inductive C : Type 2 where
  | fromA : A → C
  | higherUniv : Nat → Type → C
end
```

is rejected, even though it denotes something perfectly sensible.

This module implements the lowering used by `mutual_multiuniverse`, which
accepts such a block by translating it into ordinary declarations.  Everything
it adds to the environment is an ordinary inductive type, definition or
theorem, so no part of it asks anything new of the kernel and the worst it can
do is fail.

## The translation

1. An all-`Prop` **shadow** of the whole block, `X_i._shadow`.  Every block has
   one: the side condition on a constructor field of a `Prop`-valued inductive
   is `imax l' 0 ≤ 0`, which is vacuous, so the fields can be copied verbatim
   with member occurrences redirected to the shadow.

2. The **data** members, declared under the users' own names, against the
   shadow.  They are grouped into strongly connected components of the
   data-only dependency graph and emitted in topological order.  Each SCC is
   necessarily universe-homogeneous -- an edge `i → j` forces `l_j ≤ l_i`, so a
   cycle forces equality -- hence each is an ordinary mutual block.

3. The `Prop` members' user-facing names (reducible abbreviations for their
   shadows) and constructors, the squash maps `X._squash : X → X._shadow`, and
   a block-wide recursor `X.mutualRec` for every member.

Only the `Prop` members are mangled.  Data members are honest inductive types
under the names the user wrote, so `match`, `induction`, `cases`, `injection`,
`noConfusion`, `deriving`, `sizeOf` and the code generator all work on them as
usual, and the block's computational content stays computable.  A `Prop`
member's constructors have to be re-derived, because their fields have the
wrong types in the shadow: `A.fromB` must take a real `B`, not a `B._shadow`.

## Why the recursors come out right

* A `Prop` member of a block with at least two members is never
  large-eliminating, and the shadow has the same number of members, so it has
  exactly the original's elimination strength.  Squashing the data members
  loses nothing.  (This is also the safety boundary: we derive *universes* per
  member, never *elimination* per member.)
* A `Prop` member's iota rules are equations between proofs, so they hold by
  proof irrelevance.
* All computational content sits in the data recursors, which are the native
  recursors of the honestly-declared data members, so their iota rules hold by
  delta on `mutualRec` followed by native iota.

The one place a choice principle is unavoidable is a `Prop` member with a
constructor field that is a *function into* a data member: the data witnesses
then have to be selected pointwise, which needs `Classical.choice`.  A block
without such a field produces axiom-free recursors.
-/

namespace Lean.Elab.MultiuniverseInductive

open Lean Meta

/-! ## Auxiliary names -/

/-- The all-`Prop` shadow of member `n`. -/
def shadowName (n : Name) : Name := n ++ `_shadow

/-- `X._squash : X → X._shadow`, the map that forgets a data member's data. -/
def squashName (n : Name) : Name := n ++ `_squash

/-- Re-root a constructor name `X.c` at `newRoot`, giving `newRoot.c`. -/
def reroot (memberName newRoot ctorName : Name) : Name :=
  ctorName.replacePrefix memberName newRoot

/-- `List.replicate` as an `Array`. -/
private def rep {α : Type _} (n : Nat) (a : α) : Array α := (List.replicate n a).toArray

/-! ## Input -/

/--
The elaborated block, as `mutual_multiuniverse` hands it to the lowering.  This
is exactly the information `Lean.Elab.Command.mkInductiveDeclCore` has already
computed, with the members still represented by free variables.
-/
structure Input where
  levelParams : List Name
  /-- Number of leading section `variable`s; `numVars ≤ numParams`.  A member's
  free variable stands for the member *already applied* to these, so
  substituting a constant for it means applying that constant to them, exactly
  as `replaceIndFVarsWithConsts` does. -/
  numVars     : Nat
  numParams   : Nat
  /-- The free variables standing for the members. -/
  memberFVars : Array Expr
  memberNames : Array Name
  /-- `∀ params idxs, Sort l`, with all `numParams` binders. -/
  memberTypes : Array Expr
  ctorNames   : Array (Array Name)
  /-- `∀ params fields, X_owner params idxs`, members as free variables. -/
  ctorTypes   : Array (Array Expr)
  /-- Whether the block declares classes; if so, `SizeOf` instances and
  injectivity theorems are not generated, as for `mutual`. -/
  isClass     : Bool := false

/-! ## Block description -/

/-- What a recursive constructor field recurses into. -/
structure RecField where
  /-- Index of the member this field recurses into. -/
  member : Nat
  /-- Number of leading `∀` binders before the member is reached.  Nonzero
  means the field is a *function into* the member; these are the fields that
  force `Classical.choice` when the recursor's target is a `Prop`. -/
  arity  : Nat
  deriving Inhabited, Repr

/-- One constructor of the block. -/
structure CtorInfo where
  name      : Name
  /-- Index of the member it belongs to. -/
  owner     : Nat
  /-- `∀ params fields, X_owner params idxs`, members as free variables. -/
  type      : Expr
  numFields : Nat
  /-- One entry per field; `none` for a non-recursive field. -/
  fields    : Array (Option RecField)
  deriving Inhabited

/-- One member of the block. -/
structure MemberInfo where
  name   : Name
  /-- `∀ params idxs, Sort l`.  Contains no member occurrences. -/
  type   : Expr
  level  : Level
  isProp : Bool
  ctors  : Array CtorInfo
  deriving Inhabited

/-- The elaborated block plus the results of the analysis. -/
structure Block where
  levelParams : List Name
  numVars     : Nat
  numParams   : Nat
  memberFVars : Array Expr
  members     : Array MemberInfo
  /-- Every constructor, in block order (member 0's, then member 1's, ...).
  This is the order in which minor premises appear in every recursor. -/
  allCtors    : Array CtorInfo
  /-- Data-only SCCs, in topological order (dependencies first). -/
  sccs        : Array (Array Nat)
  /-- For each member, its SCC index, or `none` if it is a `Prop` member. -/
  sccOf       : Array (Option Nat)
  /-- One fresh universe parameter per data SCC. -/
  sccLevel    : Array Name
  /-- Whether any member is a `Prop`, i.e. whether a shadow is needed. -/
  hasProp     : Bool
  isClass     : Bool
  deriving Inhabited

def Block.size (b : Block) : Nat := b.members.size

/--
The name a member is actually declared under.  Data members keep the users'
own names and are honest inductives; only `Prop` members are mangled.
-/
def Block.realName (b : Block) (i : Nat) : Name :=
  let m := b.members[i]!
  if m.isProp then shadowName m.name else m.name

/--
The universe of `X_i`'s motive: `Prop` for a `Prop` member, the member's SCC
parameter otherwise.  Members of one SCC must share a parameter, because the
native recursor of an SCC has a single elimination universe -- and they are
universe-homogeneous anyway.
-/
def Block.motiveLevel (b : Block) (i : Nat) : Level :=
  match b.sccOf[i]! with
  | none   => .zero
  | some s => .param b.sccLevel[s]!

def Block.ownLevels (b : Block) : List Level := b.levelParams.map .param

/-- Every generated recursor carries one extra universe parameter per data SCC,
ahead of the block's own parameters, as Lean puts elimination universes first. -/
def Block.recLevelParams (b : Block) : List Name := b.sccLevel.toList ++ b.levelParams

def Block.recLevels (b : Block) : List Level := b.recLevelParams.map .param

/--
The block-wide recursor: motives and minor premises for *every* member of the
block.  Data members already have a native `X.rec`, whose motives range over
their own SCC only, so the block-wide one needs a name of its own.  A `Prop`
member has no native recursor under its user-facing name, so it additionally
answers to `X.rec`.
-/
def Block.recName (b : Block) (i : Nat) : Name := b.members[i]!.name ++ `mutualRec

/-! ## Moving between the three "worlds"

During elaboration the members are free variables.  Emitting a declaration
means replacing those free variables by constants: by the shadow names, or by
the names the members are declared under (which for a data member is the
user-facing name).  The substitution has to happen underneath the parameter
telescope, because a member free variable stands for the member applied to the
section variables.
-/

private def Block.substMembers (b : Block) (targets : Array Name) (ctorType : Expr) :
    MetaM Expr :=
  forallBoundedTelescope ctorType b.numParams fun params body => do
    let vars := params.extract 0 b.numVars
    let mut m : ExprMap Expr := {}
    for h : i in *...b.memberFVars.size do
      m := m.insert b.memberFVars[i] (mkAppN (mkConst targets[i]! b.ownLevels) vars)
    let body := body.replace fun e =>
      if !e.isFVar then none else m[e]?
    mkForallFVars params body

/-- Substitute the shadow names of all members. -/
def Block.toShadow (b : Block) (e : Expr) : MetaM Expr :=
  b.substMembers (b.members.map fun m => shadowName m.name) e

/-- Substitute the user-facing names of all members. -/
def Block.toUser (b : Block) (e : Expr) : MetaM Expr :=
  b.substMembers (b.members.map (·.name)) e

/-! ## Small helpers -/

/-- Overwrite the binder annotations of the first `bis.size` `∀`-binders. -/
private partial def forceBinderInfos (e : Expr) (bis : Array BinderInfo) (i : Nat := 0) : Expr :=
  if h : i < bis.size then
    match e with
    | .forallE n d b _ => .forallE n d (forceBinderInfos b bis (i + 1)) bis[i]
    | _ => e
  else e

/-- Replace the resulting `Sort _` of an arity by `Prop`. -/
private partial def resultToProp : Expr → Expr
  | .forallE n d b bi => .forallE n d (resultToProp b) bi
  | _ => mkSort .zero

/--
Add a plain safe definition and hand it to the code generator.  `logErrors :=
false` makes the compiler mark a declaration `noncomputable` rather than fail,
which is the right behaviour for the `Prop` members' constructors and for the
block-wide recursors (a bare recursor application is never compilable, exactly
as for `Nat.rec`).
-/
def addDef (name : Name) (levelParams : List Name) (type value : Expr)
    (hints : ReducibilityHints := .regular 0) : MetaM Unit := do
  let decl := Declaration.defnDecl { name, levelParams, type, value, hints, safety := .safe }
  addDecl decl
  compileDecl decl (logErrors := false)

/--
Add an inductive declaration and everything Lean normally builds alongside one.
This mirrors `Lean.Elab.Command.elabInductiveViews`: compile first (`sizeOf`
and friends depend on it), then the per-member constructions, then `brecOn` in
a second pass, then the block-wide ones.  `brecOn` in particular is what
structural recursion and the equation compiler need, so without it a `match`
on a member would not elaborate.
-/
def addInd (levelParams : List Name) (numParams : Nat) (indTypes : Array InductiveType)
    (isClass : Bool := false) : MetaM Unit := do
  let decl := Declaration.inductDecl levelParams numParams indTypes.toList false
  addDecl decl
  let names := indTypes.map (·.name)
  Lean.compileDecls names
  let env ← getEnv
  let hasEq   := env.contains ``Eq
  let hasHEq  := env.contains ``HEq
  let hasUnit := env.contains ``PUnit
  let hasProd := env.contains ``Prod
  let hasNat  := env.contains ``Nat
  for n in names do
    -- `mkRecOn` reuses `casesOn` where it can, so build that first
    if hasUnit then mkCasesOn n
    mkRecOn n
    if hasNat then mkCtorIdx n
    if hasNat then mkCtorElim n
    if hasUnit && hasEq && hasHEq then mkNoConfusion n
    if hasUnit && hasProd then mkBelow n
  for n in names do
    if hasUnit && hasProd then mkBRecOn n
  unless isClass do
    -- these are generated for the whole block from its first member
    mkSizeOfInstances names[0]!
    IndPredBelow.mkBelow names[0]!
    for n in names do
      mkInjectiveTheorems n

/--
`Nonempty ((w : α) ×' β w)`: a `Prop` that still remembers a data witness, and
whose eliminator lands in `Prop`, which is all the minor premises of a `Prop`
member's recursor ever need.
-/
private def mkNESig (α β : Expr) : MetaM Expr := do
  mkAppM ``Nonempty #[← mkAppOptM ``PSigma #[some α, some β]]

/--
The levels to instantiate the recursor `recName` at, given that its motives
live at `elim` and the block's own levels are `own`.  A small-eliminating
`Prop` has no separate elimination universe, so the extra level is only
prepended when the recursor actually has one.
-/
private def recLevelsFor (recName : Name) (elim : Level) (own : List Level) :
    MetaM (List Level) := do
  let info ← getConstInfoRec recName
  if info.levelParams.length == own.length then
    return own
  else
    return elim :: own

/-! ## Analysis

Deciding *whether* a block can be lowered, and rejecting the shapes the
lowering cannot express.
-/

/--
Condensation of the data-only dependency graph, in topological order
(dependencies first).  Returns the components and, for each member, its
component index (`none` for a `Prop` member).

`n` is the number of members of one `mutual` block, so the cubic reachability
closure is not worth optimising.
-/
def computeSCCs (n : Nat) (isData : Array Bool) (edges : Array (Array Bool)) :
    Array (Array Nat) × Array (Option Nat) := Id.run do
  -- transitive closure
  let mut r := edges
  for k in *...n do
    for i in *...n do
      if r[i]![k]! then
        for j in *...n do
          if r[k]![j]! && !r[i]![j]! then
            r := r.set! i (r[i]!.set! j true)
  -- raw components: `i ~ j` iff mutually reachable
  let mut compOf : Array (Option Nat) := rep n none
  let mut comps : Array (Array Nat) := #[]
  for i in *...n do
    if isData[i]! && compOf[i]!.isNone then
      let mut c := #[]
      for j in *...n do
        if isData[j]! && compOf[j]!.isNone && (j == i || (r[i]![j]! && r[j]![i]!)) then
          c := c.push j
      for j in c do
        compOf := compOf.set! j (some comps.size)
      comps := comps.push c
  -- topologically order the condensation: a component may be emitted once
  -- every component it depends on has been emitted
  let m := comps.size
  let mut emitted : Array Bool := rep m false
  let mut order : Array Nat := #[]
  for _pass in *...m do
    if order.size == m then
      break
    for a in *...m do
      if !emitted[a]! then
        let mut ok := true
        for i in comps[a]! do
          for j in *...n do
            if r[i]![j]! then
              if let some bc := compOf[j]! then
                if bc != a && !emitted[bc]! then
                  ok := false
        if ok then
          emitted := emitted.set! a true
          order := order.push a
  -- renumber into topological order
  let mut newOf : Array Nat := rep m 0
  for pos in *...order.size do
    newOf := newOf.set! order[pos]! pos
  let sccs := order.map (comps[·]!)
  let sccOf := compOf.map (fun o => o.map (newOf[·]!))
  return (sccs, sccOf)

/-- Pick `n` level parameter names not clashing with `avoid`. -/
def freshLevelNames (avoid : List Name) (n : Nat) : Array Name := Id.run do
  let cands : Array Name := #[`u, `v, `w, `x, `y, `z]
  let mut used := avoid
  let mut out := #[]
  let mut next := 0
  for i in *...n do
    let mut nm := if h : i < cands.size then cands[i] else Name.mkSimple s!"u_{i}"
    while used.contains nm do
      next := next + 1
      nm := Name.mkSimple s!"u_{next}"
    used := nm :: used
    out := out.push nm
  return out

/-- Does `e` mention any of the block's members? -/
private def mentionsMember (fvars : Array Expr) (e : Expr) : Bool :=
  fvars.any fun f => e.containsFVar f.fvarId!

/--
Classify one constructor field.

Accepts a non-recursive field (no member occurrence at all), or a field of the
form `∀ ys, X_j params idxs` where neither the `ys` domains nor the `idxs`
mention any member.  Everything else -- in particular a *nested* occurrence
such as `List (X_j ...)` -- is rejected: the shadow has no data to rebuild such
a field from without lowering the surrounding type constructor too.
-/
private def analyzeField (inp : Input) (fieldTy : Expr) (ctor : Name) (k : Nat) :
    MetaM (Option RecField) := do
  if !mentionsMember inp.memberFVars fieldTy then
    return none
  forallTelescope fieldTy fun ys body => do
    for y in ys do
      if mentionsMember inp.memberFVars (← inferType y) then
        throwError m!"Unsupported constructor field in `mutual_multiuniverse` block: field \
          {k + 1} of `{ctor}` takes an argument whose type mentions a member of the block"
          ++ .note "This is not a strictly positive occurrence, so the lowering has nothing \
            to translate it to"
    let some j := inp.memberFVars.findIdx? (· == body.getAppFn)
      | throwError m!"Unsupported constructor field in `mutual_multiuniverse` block: field \
          {k + 1} of `{ctor}` mentions a member of the block in a nested position, in the \
          type{indentExpr fieldTy}"
          ++ .note "Nested occurrences are not supported: the shadow of a data member carries \
            no data, so there is nothing to rebuild such a field from without lowering the \
            surrounding type as well"
    for a in body.getAppArgs do
      if mentionsMember inp.memberFVars a then
        throwError m!"Unsupported constructor field in `mutual_multiuniverse` block: field \
          {k + 1} of `{ctor}` has a type that applies a member of the block to an argument \
          mentioning another one, in the type{indentExpr fieldTy}"
          ++ .note "Nested occurrences are not supported"
    return some { member := j, arity := ys.size }

/--
Reject a constructor whose *result indices* depend on a field of data-member
type.

The lowering identifies the shadow world and the real world at every index
position: the shadow constructor is applied to shadow fields, the real one to
real fields, and the two must land at the same indices.  Fields that are not
members, and fields of `Prop`-member type, are literally the same variable in
both worlds; a field of data-member type is not.

This is a defensive check.  Reaching it needs a function from a member of the
block into an index type, and there is none to be had: headers are elaborated
before any member is in scope, so no member's indices can mention another
member, and nested occurrences are rejected outright.
-/
private def checkIndices (isProp : Array Bool) (c : CtorInfo)
    (fields : Array Expr) (idxs : Array Expr) : MetaM Unit := do
  let mut bad : Array Expr := #[]
  for k in *...c.numFields do
    if let some rf := c.fields[k]! then
      if !isProp[rf.member]! then
        bad := bad.push fields[k]!
  if bad.isEmpty then return
  for idx in idxs do
    for f in bad do
      if idx.containsFVar f.fvarId! then
        throwError m!"Unsupported constructor in `mutual_multiuniverse` block: `{c.name}` \
          computes a result index from a field whose type is a non-`Prop` member of the block"
          ++ .note "The lowering cannot keep the shadow block and the real one in step across \
            such an index, since the shadow's data fields carry no data"

/-- Build a `Block` from freshly elaborated inductive data, or throw. -/
def analyze (inp : Input) : MetaM Block := do
  let n := inp.memberTypes.size
  -- 1. the members' universes
  let mut levels : Array Level := #[]
  let mut isProp : Array Bool := #[]
  for i in *...n do
    let l ← forallTelescope inp.memberTypes[i]! fun _ body => do
      let .sort l := (← whnf body)
        | throwError "The type of `{inp.memberNames[i]!}` does not end in a sort:\
            {indentExpr inp.memberTypes[i]!}"
      return l
    levels := levels.push l
    isProp := isProp.push (match l.normalize with | .zero => true | _ => false)
  -- 2. the constructors, and the data-only dependency graph
  let mut members : Array MemberInfo := #[]
  let mut allCtors : Array CtorInfo := #[]
  let mut edges : Array (Array Bool) := rep n (rep n false)
  for i in *...n do
    let mut ctors : Array CtorInfo := #[]
    for j in *...inp.ctorNames[i]!.size do
      let cname := inp.ctorNames[i]![j]!
      let cty := inp.ctorTypes[i]![j]!
      let c ← forallBoundedTelescope cty (some inp.numParams) fun _params inner =>
        forallTelescope inner fun fields result => do
          let mut fs : Array (Option RecField) := #[]
          for k in *...fields.size do
            fs := fs.push (← analyzeField inp (← inferType fields[k]!) cname k)
          let c : CtorInfo :=
            { name := cname, owner := i, type := cty, numFields := fields.size, fields := fs }
          let args := result.getAppArgs
          checkIndices isProp c fields (args.extract inp.numParams args.size)
          return c
      if !isProp[i]! then
        for f? in c.fields do
          if let some rf := f? then
            if !isProp[rf.member]! then
              edges := edges.set! i (edges[i]!.set! rf.member true)
      ctors := ctors.push c
      allCtors := allCtors.push c
    members := members.push
      { name := inp.memberNames[i]!, type := inp.memberTypes[i]!,
        level := levels[i]!, isProp := isProp[i]!, ctors }
  -- 3. condensation of the data-only graph
  let isData := isProp.map not
  let (sccs, sccOf) := computeSCCs n isData edges
  let sccLevel := freshLevelNames inp.levelParams sccs.size
  return { levelParams := inp.levelParams, numVars := inp.numVars, numParams := inp.numParams,
           memberFVars := inp.memberFVars, members, allCtors,
           sccs, sccOf, sccLevel, hasProp := isProp.any id, isClass := inp.isClass }

/-- Is every member at the same universe?  Then the block is an ordinary
`mutual` block and the lowering should not touch it. -/
def Block.isHomogeneous (b : Block) : Bool :=
  b.members.all fun m => m.level.normalize == b.members[0]!.level.normalize

/-! ## The lowering

Emission order; each step only mentions constants emitted by earlier steps.

0. if the block is homogeneous, emit it natively and stop;
1. `X_i._shadow`   -- the all-`Prop` shadow of the whole block;
2. `X_i` for `Prop` members -- reducible abbreviations for their shadows;
3. `X_i` for data members   -- honest inductives, one SCC at a time, in
                              topological order;
4. `X_i._squash`   -- `X_i → X_i._shadow`, one SCC at a time;
5. `X_i.c` for `Prop` members -- the user-facing constructors;
6. `X_i.mutualRec` for `Prop` members -- from the shadow recursor;
7. `X_i.mutualRec` for data members, in SCC order -- from the native recursors.

Step 6 only mentions data *constructors*, never data recursors, so 6 and 7 do
not form a cycle.
-/

/-- Walk `n` `∀`-binders of `ty`, building an argument for each via `mk` and
instantiating as we go, so later domains see the earlier arguments. -/
private def buildArgs (ty : Expr) (n : Nat) (mk : Nat → Expr → MetaM Expr) :
    MetaM (Array Expr) := do
  let mut ty := ty
  let mut args := #[]
  for i in *...n do
    let ty' ← whnf ty
    let .forallE _ d body _ := ty'
      | throwError "(internal) `mutual_multiuniverse`: expected {n} arguments in\
          {indentExpr ty}"
    let a ← mk i d
    args := args.push a
    ty := body.instantiate1 a
  return args

/-- The constructors of SCC `s`, as indices into `b.allCtors`, in the order the
native recursor of that SCC expects its minor premises. -/
private def sccCtorIndices (b : Block) (s : Nat) : Array Nat := Id.run do
  let mut out := #[]
  for j in b.sccs[s]! do
    for q in *...b.allCtors.size do
      if b.allCtors[q]!.owner == j then
        out := out.push q
  return out

/-- `X_i.mutualRec := X_i.rec`, for a block whose native recursor already ranges
over every member.  Keeps the generated API the same on the native path as on
the lowered one. -/
private def aliasNativeRecs (b : Block) : MetaM Unit := do
  for i in *...b.size do
    let rn := b.members[i]!.name ++ `rec
    let info ← getConstInfoRec rn
    addDef (b.recName i) info.levelParams info.type
      (mkConst rn (info.levelParams.map Level.param))

/-- A homogeneous block is an ordinary `mutual` block; emit it unchanged, so
that `mutual_multiuniverse` is a strict superset of `mutual`. -/
private def emitNative (b : Block) : MetaM Unit := do
  let mut indTypes : Array InductiveType := #[]
  for i in *...b.size do
    let m := b.members[i]!
    let ctors ← m.ctors.mapM fun c =>
      return ({ name := c.name, type := ← b.toUser c.type } : Constructor)
    indTypes := indTypes.push { name := m.name, type := m.type, ctors := ctors.toList }
  addInd b.levelParams b.numParams indTypes b.isClass
  aliasNativeRecs b

/-- The all-`Prop` shadow.  Only the resulting sorts change: constructor fields
are copied verbatim, with member occurrences redirected to the shadow, which is
legal because a `Prop`-valued inductive imposes no constraint on its fields. -/
private def emitShadow (b : Block) : MetaM Unit := do
  let mut indTypes : Array InductiveType := #[]
  for i in *...b.size do
    let m := b.members[i]!
    let sn := shadowName m.name
    let ctors ← m.ctors.mapM fun c =>
      return ({ name := reroot m.name sn c.name, type := ← b.toShadow c.type } : Constructor)
    indTypes := indTypes.push { name := sn, type := resultToProp m.type, ctors := ctors.toList }
  addInd b.levelParams b.numParams indTypes

/-- A `Prop` member *is* its shadow -- the shadow only squashes data members --
so its user-facing name is a reducible abbreviation.  These come before the
data members, whose constructors mention them. -/
private def emitPropAliases (b : Block) : MetaM Unit := do
  for i in *...b.size do
    let m := b.members[i]!
    if m.isProp then
      addDef m.name b.levelParams m.type (mkConst (b.realName i) b.ownLevels) .abbrev
      setReducibleAttribute m.name

/--
One SCC of the data-only dependency graph, declared under the users' own names.
Its members are necessarily at the same universe (an edge `i → j` forces
`l_j ≤ l_i`, so a cycle forces equality), hence this is an ordinary,
homogeneous mutual block.  Fields of `Prop`-member type refer to the aliases,
which the kernel unfolds to the shadow; being outside the block, they impose no
positivity obligation.
-/
private def emitDataSCC (b : Block) (s : Nat) : MetaM Unit := do
  let mut indTypes : Array InductiveType := #[]
  for i in b.sccs[s]! do
    let m := b.members[i]!
    let ctors ← m.ctors.mapM fun c =>
      return ({ name := c.name, type := ← b.toUser c.type } : Constructor)
    indTypes := indTypes.push { name := m.name, type := m.type, ctors := ctors.toList }
  addInd b.levelParams b.numParams indTypes b.isClass

/-- `X_j._squash params idxs v`, lifted pointwise through any leading `∀`s of
`v`'s type. -/
private def squashApply (b : Block) (j : Nat) (v : Expr) : MetaM Expr := do
  forallTelescope (← inferType v) fun ys body => do
    let sq := mkConst (squashName b.members[j]!.name) b.ownLevels
    mkLambdaFVars ys (mkAppN sq (body.getAppArgs ++ #[mkAppN v ys]))

/-- Minor premise for `X_i._squash`: rebuild the constructor in the shadow. -/
private def mkSquashMinor (b : Block) (s : Nat) (params : Array Expr) (c : CtorInfo)
    (minorTy : Expr) : MetaM Expr := do
  forallTelescope minorTy fun args _ => do
    let fields := args.extract 0 c.numFields
    let ihs := args.extract c.numFields args.size
    let mut gs := #[]
    let mut p := 0
    for k in *...c.numFields do
      match c.fields[k]! with
      | none => gs := gs.push fields[k]!
      | some rf =>
        if b.members[rf.member]!.isProp then
          -- already a shadow inhabitant: `X_j` *is* `X_j._shadow`
          gs := gs.push fields[k]!
        else if b.sccOf[rf.member]! == some s then
          -- the induction hypothesis *is* the shadow image
          gs := gs.push ihs[p]!
          p := p + 1
        else
          -- an earlier SCC: its squash map is already defined
          gs := gs.push (← squashApply b rf.member fields[k]!)
    let m := b.members[c.owner]!
    let sctor := mkConst (reroot m.name (shadowName m.name) c.name) b.ownLevels
    mkLambdaFVars args (mkAppN sctor (params ++ gs))

private def emitSquashSCC (b : Block) (s : Nat) : MetaM Unit := do
  let ctorIdx := sccCtorIndices b s
  for i in b.sccs[s]! do
    let m := b.members[i]!
    forallBoundedTelescope m.type (some b.numParams) fun params _ => do
      let dataOf (j : Nat) (jidxs : Array Expr) : Expr :=
        mkAppN (mkConst b.members[j]!.name b.ownLevels) (params ++ jidxs)
      let shadowOf (j : Nat) (jidxs : Array Expr) : Expr :=
        mkAppN (mkConst (shadowName b.members[j]!.name) b.ownLevels) (params ++ jidxs)
      let mut motives := #[]
      for j in b.sccs[s]! do
        let aj ← instantiateForall b.members[j]!.type params
        let mot ← forallTelescope aj fun jidxs _ =>
          withLocalDeclD `t (dataOf j jidxs) fun tv =>
            mkLambdaFVars (jidxs ++ #[tv]) (shadowOf j jidxs)
        motives := motives.push mot
      let recName := m.name ++ `rec
      let recFn := mkConst recName (← recLevelsFor recName .zero b.ownLevels)
      let ty0 ← instantiateForall (← inferType recFn) params
      let ty1 ← instantiateForall ty0 motives
      let minors ← buildArgs ty1 ctorIdx.size fun q minorTy =>
        mkSquashMinor b s params b.allCtors[ctorIdx[q]!]! minorTy
      let ai ← instantiateForall m.type params
      forallTelescope ai fun idxs _ =>
        withLocalDeclD `t (dataOf i idxs) fun tv => do
          let all := params ++ idxs ++ #[tv]
          let ty ← mkForallFVars all (shadowOf i idxs)
          let val ← mkLambdaFVars all (mkAppN recFn (params ++ motives ++ minors ++ idxs ++ #[tv]))
          addDef (squashName m.name) b.levelParams ty val

/--
The `Prop` members' constructors.  The data members' constructors are the
native ones and need no help; a `Prop` member's shadow constructor wants shadow
arguments, so each data field is sent through its squash map.
-/
private def emitPropCtors (b : Block) : MetaM Unit := do
  for i in *...b.size do
    let m := b.members[i]!
    if !m.isProp then continue
    for c in m.ctors do
      let cty ← b.toUser c.type
      forallBoundedTelescope cty (some b.numParams) fun params inner =>
        forallTelescope inner fun fields _ => do
          let mut gs := #[]
          for k in *...c.numFields do
            match c.fields[k]! with
            | some rf =>
              if b.members[rf.member]!.isProp then
                gs := gs.push fields[k]!
              else
                gs := gs.push (← squashApply b rf.member fields[k]!)
            | none => gs := gs.push fields[k]!
          let realCtor := mkConst (reroot m.name (b.realName i) c.name) b.ownLevels
          -- reuse the elaborated type verbatim, so the constructor keeps the
          -- binder annotations it would have got from `mutual`
          addDef c.name b.levelParams cty
            (← mkLambdaFVars (params ++ fields) (mkAppN realCtor (params ++ gs)))

/-! ### Recursors

Every generated recursor has the *same* signature apart from its major premise
and result:

```
{params} {motive_1 .. motive_n} (case_1 .. case_K) {idxs} (t : X_i idxs)
  : motive_i idxs t
```

with `motive_j` at `Prop` for a `Prop` member and at that member's SCC universe
otherwise.  This uniformity is what lets a data recursor plug `X_j.mutualRec`
in as the induction hypothesis for a field it has no native IH for: the
arguments it already has are exactly the ones `X_j.mutualRec` wants.
-/

/-- The type of the minor premise for constructor `c`: all fields, then one
induction hypothesis per recursive field, in field order. -/
private def mkMinorType (b : Block) (params motives : Array Expr) (c : CtorInfo) :
    MetaM Expr := do
  let inner ← instantiateForall (← b.toUser c.type) params
  forallTelescope inner fun fields result => do
    let args := result.getAppArgs
    let idxs := args.extract b.numParams args.size
    let ctorApp := mkAppN (mkConst c.name b.ownLevels) (params ++ fields)
    let mut concl := mkAppN motives[c.owner]! (idxs ++ #[ctorApp])
    let mut ihs : Array (Name × Expr) := #[]
    for k in *...c.numFields do
      if let some rf := c.fields[k]! then
        let ih ← forallTelescope (← inferType fields[k]!) fun ys fbody => do
          let fargs := fbody.getAppArgs
          let fidxs := fargs.extract b.numParams fargs.size
          mkForallFVars ys (mkAppN motives[rf.member]! (fidxs ++ #[mkAppN fields[k]! ys]))
        ihs := ihs.push (Name.mkSimple s!"ih_{k + 1}", ih)
    -- no induction hypothesis is ever referred to, so plain `forallE` is safe
    for (nm, t) in ihs.reverse do
      concl := .forallE nm t concl .default
    mkForallFVars fields concl

/-- Set up the common outer telescope and hand the body builder the pieces. -/
private def withRecTelescope (b : Block) (i : Nat)
    (mkBody : Array Expr → Array Expr → Array Expr → Array Expr → Expr → MetaM Expr) :
    MetaM (Expr × Expr) := do
  forallBoundedTelescope b.members[i]!.type (some b.numParams) fun params _ => do
    let userOf (j : Nat) (jidxs : Array Expr) : Expr :=
      mkAppN (mkConst b.members[j]!.name b.ownLevels) (params ++ jidxs)
    let mut motiveDecls : Array (Name × BinderInfo × (Array Expr → MetaM Expr)) := #[]
    for j in *...b.size do
      let aj ← instantiateForall b.members[j]!.type params
      let mt ← forallTelescope aj fun jidxs _ =>
        withLocalDeclD `t (userOf j jidxs) fun tv =>
          mkForallFVars (jidxs ++ #[tv]) (mkSort (b.motiveLevel j))
      motiveDecls := motiveDecls.push
        (Name.mkSimple s!"motive_{j + 1}", .implicit, fun _ => pure mt)
    withLocalDecls motiveDecls fun motives => do
      let mut minorDecls : Array (Name × BinderInfo × (Array Expr → MetaM Expr)) := #[]
      for q in *...b.allCtors.size do
        let mt ← mkMinorType b params motives b.allCtors[q]!
        minorDecls := minorDecls.push
          (Name.mkSimple s!"case_{q + 1}", .default, fun _ => pure mt)
      withLocalDecls minorDecls fun minors => do
        let ai ← instantiateForall b.members[i]!.type params
        forallTelescope ai fun idxs _ =>
          withLocalDeclD `t (userOf i idxs) fun major => do
            let body ← mkBody params motives minors idxs major
            let all := params ++ motives ++ minors ++ idxs ++ #[major]
            let ty ← mkForallFVars all (mkAppN motives[i]! (idxs ++ #[major]))
            let bis := rep b.numParams BinderInfo.implicit
                    ++ rep b.size BinderInfo.implicit
                    ++ rep b.allCtors.size BinderInfo.default
                    ++ rep idxs.size BinderInfo.implicit
                    ++ #[BinderInfo.default]
            return (forceBinderInfos ty bis, ← mkLambdaFVars all body)

/-- `X_j.mutualRec` applied at the current motives and minors, lifted pointwise
through any leading `∀`s of `v`'s type. -/
private def recCall (b : Block) (params motives minors : Array Expr) (j : Nat) (v : Expr) :
    MetaM Expr := do
  forallTelescope (← inferType v) fun ys body => do
    let allArgs := body.getAppArgs
    let jidxs := allArgs.extract b.numParams allArgs.size
    let r := mkConst (b.recName j) b.recLevels
    mkLambdaFVars ys (mkAppN r (params ++ motives ++ minors ++ jidxs ++ #[mkAppN v ys]))

/--
Build the body of a shadow minor premise, walking the constructor's fields.

The shadow's fields for data members are useless -- they carry no data -- so we
*discard* them and take the real element out of the corresponding induction
hypothesis, whose motive was chosen to be `Nonempty ((w : X_j) ×' motive_j w)`
precisely so that it would still contain one.  This is legal because everything
built here is a `Prop`.
-/
private partial def propMinorBody (b : Block) (params motives minors : Array Expr)
    (c : CtorInfo) (q : Nat) (sf sih : Array Expr) (target : Expr)
    (k ihPos : Nat) (realF realIH : Array Expr) : MetaM Expr := do
  if k ≥ c.numFields then
    let minorApp := mkAppN minors[q]! (realF ++ realIH)
    let m := b.members[c.owner]!
    if m.isProp then
      -- the shadow field and the real field are equal by proof irrelevance
      return minorApp
    else
      -- repackage as `⟨⟨X_m.c realF, case realF realIH⟩⟩`
      let sigTy := target.appArg!
      let sargs := sigTy.getAppArgs
      let ctorApp := mkAppN (mkConst c.name b.ownLevels) (params ++ realF)
      let mk ← mkAppOptM ``PSigma.mk
        #[some sargs[0]!, some sargs[1]!, some ctorApp, some minorApp]
      mkAppOptM ``Nonempty.intro #[some sigTy, some mk]
  else
    let cont := propMinorBody b params motives minors c q sf sih target
    match c.fields[k]! with
    | none => cont (k + 1) ihPos (realF.push sf[k]!) realIH
    | some rf =>
      let ih := sih[ihPos]!
      if b.members[rf.member]!.isProp then
        -- `X_j` *is* `X_j._shadow`, so the shadow field and IH are already right
        cont (k + 1) (ihPos + 1) (realF.push sf[k]!) (realIH.push ih)
      else if rf.arity == 0 then
        -- destructure the witness; `Nonempty.rec` lands in `Prop`, which the
        -- target is, so no choice principle is needed
        let ihTy ← whnf (← inferType ih)
        let sigTy := ihTy.appArg!
        let lvl ← getLevel sigTy
        withLocalDeclD (Name.mkSimple s!"w_{k + 1}") sigTy fun wv => do
          let bb ← mkAppM ``PSigma.fst #[wv]
          let pp ← mkAppM ``PSigma.snd #[wv]
          let rest ← cont (k + 1) (ihPos + 1) (realF.push bb) (realIH.push pp)
          let f ← mkLambdaFVars #[wv] rest
          let mot := Expr.lam `h ihTy target .default
          return mkAppN (mkConst ``Nonempty.rec [lvl]) #[sigTy, mot, f, ih]
      else
        -- a function *into* a data member: the witnesses have to be selected
        -- pointwise, which is the one place `Classical.choice` is unavoidable
        let ihTy ← inferType ih
        let kf ← forallTelescope ihTy fun ys neBody => do
          let sigTy := (← whnf neBody).appArg!
          let lvl ← getLevel sigTy
          mkLambdaFVars ys (mkAppN (mkConst ``Classical.choice [lvl]) #[sigTy, mkAppN ih ys])
        let bb ← forallTelescope ihTy fun ys _ => do
          mkLambdaFVars ys (← mkAppM ``PSigma.fst #[mkAppN kf ys])
        let pp ← forallTelescope ihTy fun ys _ => do
          mkLambdaFVars ys (← mkAppM ``PSigma.snd #[mkAppN kf ys])
        cont (k + 1) (ihPos + 1) (realF.push bb) (realIH.push pp)

private def mkPropRecBody (b : Block) (i : Nat)
    (params motives minors idxs : Array Expr) (major : Expr) : MetaM Expr := do
  let mut smotives := #[]
  for j in *...b.size do
    let aj ← instantiateForall b.members[j]!.type params
    let mot ← forallTelescope aj fun jidxs _ => do
      let sTy := mkAppN (mkConst (shadowName b.members[j]!.name) b.ownLevels) (params ++ jidxs)
      withLocalDeclD `t sTy fun tv => do
        let body ←
          if b.members[j]!.isProp then
            pure (mkAppN motives[j]! (jidxs ++ #[tv]))
          else
            let dTy := mkAppN (mkConst b.members[j]!.name b.ownLevels) (params ++ jidxs)
            withLocalDeclD `w dTy fun wv => do
              mkNESig dTy (← mkLambdaFVars #[wv] (mkAppN motives[j]! (jidxs ++ #[wv])))
        mkLambdaFVars (jidxs ++ #[tv]) body
    smotives := smotives.push mot
  let recName := shadowName b.members[i]!.name ++ `rec
  let recFn := mkConst recName (← recLevelsFor recName .zero b.ownLevels)
  let ty0 ← instantiateForall (← inferType recFn) params
  let ty1 ← instantiateForall ty0 smotives
  let sminors ← buildArgs ty1 b.allCtors.size fun q minorTy => do
    let c := b.allCtors[q]!
    forallTelescope minorTy fun args target => do
      let sf := args.extract 0 c.numFields
      let sih := args.extract c.numFields args.size
      let body ← propMinorBody b params motives minors c q sf sih (← whnf target) 0 0 #[] #[]
      mkLambdaFVars args body
  return mkAppN recFn (params ++ smotives ++ sminors ++ idxs ++ #[major])

private def mkDataRecBody (b : Block) (i : Nat)
    (params motives minors idxs : Array Expr) (major : Expr) : MetaM Expr := do
  let some s := b.sccOf[i]!
    | throwError "(internal) `mutual_multiuniverse`: data member without an SCC"
  let mut nmotives := #[]
  for j in b.sccs[s]! do
    let aj ← instantiateForall b.members[j]!.type params
    let mot ← forallTelescope aj fun jidxs _ => do
      let dTy := mkAppN (mkConst b.members[j]!.name b.ownLevels) (params ++ jidxs)
      withLocalDeclD `t dTy fun tv =>
        mkLambdaFVars (jidxs ++ #[tv]) (mkAppN motives[j]! (jidxs ++ #[tv]))
    nmotives := nmotives.push mot
  let recName := b.members[i]!.name ++ `rec
  let recFn := mkConst recName (← recLevelsFor recName (b.motiveLevel i) b.ownLevels)
  let ty0 ← instantiateForall (← inferType recFn) params
  let ty1 ← instantiateForall ty0 nmotives
  let ctorIdx := sccCtorIndices b s
  let nminors ← buildArgs ty1 ctorIdx.size fun q minorTy => do
    let gq := ctorIdx[q]!
    let c := b.allCtors[gq]!
    forallTelescope minorTy fun args _ => do
      let fields := args.extract 0 c.numFields
      let nih := args.extract c.numFields args.size
      let mut userIH := #[]
      let mut p := 0
      for k in *...c.numFields do
        if let some rf := c.fields[k]! then
          if b.sccOf[rf.member]! == some s then
            -- the native recursor already provides this one
            userIH := userIH.push nih[p]!
            p := p + 1
          else
            -- a `Prop` member, or a data member of an earlier SCC: its
            -- block-wide recursor is already defined and takes exactly our
            -- arguments
            userIH := userIH.push (← recCall b params motives minors rf.member fields[k]!)
      mkLambdaFVars args (mkAppN minors[gq]! (fields ++ userIH))
  return mkAppN recFn (params ++ nmotives ++ nminors ++ idxs ++ #[major])

private def emitRec (b : Block) (i : Nat) : MetaM Unit := do
  let m := b.members[i]!
  let (ty, val) ← withRecTelescope b i fun params motives minors idxs major =>
    if m.isProp then
      mkPropRecBody b i params motives minors idxs major
    else
      mkDataRecBody b i params motives minors idxs major
  addDef (b.recName i) b.recLevelParams ty val
  -- a `Prop` member has no native recursor under its user-facing name, so the
  -- block-wide one may as well also answer to `X.rec`
  if m.isProp then
    addDef (m.name ++ `rec) b.recLevelParams ty val

/--
Lower an elaborated `mutual_multiuniverse` block to ordinary declarations.

A homogeneous block is emitted natively, so `mutual_multiuniverse` accepts
everything `mutual` does and means the same thing by it.
-/
def lower (inp : Input) : MetaM Unit := do
  let b ← analyze inp
  if b.isHomogeneous then
    emitNative b
    return
  if b.hasProp then
    emitShadow b
    emitPropAliases b
  for s in *...b.sccs.size do
    emitDataSCC b s
  if b.hasProp then
    for s in *...b.sccs.size do
      emitSquashSCC b s
    emitPropCtors b
    for i in *...b.size do
      if b.members[i]!.isProp then
        emitRec b i
  for s in *...b.sccs.size do
    for i in b.sccs[s]! do
      emitRec b i

end Lean.Elab.MultiuniverseInductive

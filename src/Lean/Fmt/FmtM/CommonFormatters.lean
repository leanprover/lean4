/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Marc Huisinga
-/
module

prelude
public import Lean.Fmt.FmtM.Basic
public meta import Lean.Parser.Term.Basic
meta import Lean.Parser.Term
meta import Lean.Parser.Command
import Init.Data
import Init.While
import Lean.Fmt.Util.Basic

namespace Lean.Fmt

public def fmtProjLike (lhs : TaggedDoc) (dotTk : Syntax) (field : Syntax) : FmtM TaggedDoc := do
  let dotTk ← fmt dotTk
  let field ← fmt field
  return propagateStickyness lhs fun lhs => mkSelfDelimited <| Layouts.atomic #[lhs, dotTk, field]

public def allowAppArgFill : Syntax → Bool
  | `(Parser.Term.fun| $_:fun) => false
  | `(Parser.Term.paren| ($_:fun)) => false
  | `(Parser.Term.namedArgument| ($_:ident := $_:fun)) => false
  | _ => true

public def fmtFixedApp'
    (f : TaggedDoc) (args : Array Syntax)
    (format : Layouts.Types.ApplicationFormat := {
      parenthesize := true
      respectPseudoAlignment := true
    })
    : FmtM (TaggedDoc × Array TaggedDoc) := do
  let mut args : Array (Fillable TaggedDoc) ←
    args.mapM fun arg => do return ({ v := ← fmt arg, allowFill := allowAppArgFill arg })
  if args[0...args.size - 1].all (·.allowFill) then
    args := args.modify (args.size - 1) fun lastArg => { lastArg with allowFill := true }
  let app := Layouts.applicationWithSomeFilled (format := format) <| #[⟨f, true⟩] ++ args
  return (app, args.map (·.v))

public def fmtFixedApp
    (f : TaggedDoc) (args : Array Syntax)
    (format : Layouts.Types.ApplicationFormat := {
      parenthesize := true
      respectPseudoAlignment := true
    })
    : FmtM TaggedDoc := do
  let (app, _) ← fmtFixedApp' f args format
  return app

public def fmtAppLike (terms : Array Syntax) : FmtM TaggedDoc := do
  if terms.isEmpty then
    return empty
  let fStx := terms[0]!
  let args := terms[1...*].toArray
  let mut (f, format) ← do
    match fStx with
    | `($lhs:term.%$dotTk$field) =>
      let lhs ← fmt lhs
      let format : Layouts.Types.ApplicationFormat := {
        sparse := lhs.isBracketed
        parenthesize := true
        respectPseudoAlignment := true
      }
      pure (← fmtProjLike lhs dotTk field, format)
    | _ =>
      pure (← fmt fStx, { parenthesize := true, respectPseudoAlignment := true })
  let (app, args') ← fmtFixedApp' f args format
  if args'.size = 1 then
    let arg := args'[0]!
    if let some stickyArg := getSticky? arg then
      if propagatesRhsStickiness (← read).env ⟨fStx⟩ then
        return sticky app app stickyArg.kind
  return app

public def fmtArrayLit (lbTk : Syntax) (elems : Syntax.TSepArray ks ",") (rbTk : Syntax)
    : FmtM TaggedDoc := do
  let lbTk ← fmt lbTk
  let groups ← fmtTSepArrayTrailingGroups elems
  let rbTk ← fmt rbTk
  if let #[.group ⟨#[elem]⟩] := groups then
    if !elem.needsAppBrackets then
      return Layouts.bracketed lbTk elem rbTk .dense
  let groups :=
    groups.map fun
      | .group g => Layouts.sepArray g <| .fillUsingSpacedSep none .retainTrailingSep
      | .trailing t => t
  let elems := join groups
  return Layouts.bracketed lbTk elems rbTk <| .sparse «break» (stickynessKind := .coequal)

public def fmtSeq (seq : Syntax.TSepArray ks sep) (nestedKind? : Option SyntaxNodeKind)
    : FmtM TaggedDoc := do
  if let some nestedKind := nestedKind? then
    let seqElems := seq.getElems
    if seqElems.size = 1 && seqElems[0]!.raw.getKind == nestedKind then
      -- We deliberately skip `withPosition` here to support sticky nested sequences.
      return ← fmt seqElems[0]!
  let groups ← fmtTSepArrayTrailingGroups seq
  let groups := applyPseudoDedented groups
  let multiLineAlt :=
    join <| groups.map fun
      | .group g => Layouts.sepLines g (includeSeps := false)
      | .trailing t => t
  let mut r := multiLineAlt
  if groups.size = 1 then
    if let .group g := groups[0]! then
      let singleLineAlt := flattened <| Layouts.sepArray g <| .joinUsingSep none space
      r := oneOf #[singleLineAlt, r]
  return withPosition r
where
  applyPseudoDedented (groups : Array (TrailingGroup sep)) : Array (TrailingGroup sep) := Id.run do
    for i in (0...groups.size) do
      let i := groups.size - i - 1
      let .group g := groups[i]!
        | continue
      let j :=
        if g.elemsAndSeps.size % 2 = 0 then
          g.elemsAndSeps.size - 2
        else
          g.elemsAndSeps.size - 1
      let some pseudoDedented := getPseudoDedented? g.elemsAndSeps[j]!
        | break
      return groups.modify i fun
        | .group g => .group ⟨g.elemsAndSeps.set! j pseudoDedented.dedentedVariant⟩
        | _ => unreachable!
    return groups

public meta def explicitBinderF := Parser.Term.explicitBinder
public meta def implicitBinderF := Parser.Term.implicitBinder
public meta def strictImplicitBinderF := Parser.Term.strictImplicitBinder

public abbrev binderKinds : List Name := [
  `ident,
  ``Parser.Term.hole,
  ``Parser.Term.bracketedBinder
]

private inductive BinderKind where
  | explicit
  | implicit
  | instance
deriving BEq, Inhabited, Repr, Hashable

private def BinderKind.classify (binder : TSyntax binderKinds) : BinderKind :=
  match binder.raw with
  | `(explicitBinderF| ($ids* $[: $type?:term]? $[$default?]?)) =>
    c ids .explicit
  | `(implicitBinderF| {$ids* $[: $type?:term]?})
  | `(strictImplicitBinderF| { {$ids* $[: $type?:term]?} })
  | `(strictImplicitBinderF| { {$ids* $[: $type?:term]?⦄)
  | `(strictImplicitBinderF| ⦃$ids* $[: $type?:term]?} })
  | `(strictImplicitBinderF| ⦃$ids* $[: $type?:term]?⦄) =>
    c ids .implicit
  | `(Parser.Term.instBinder| [$[$_ :]? $_]) =>
    .instance
  | _ =>
    -- `ident` and `hole` binders
    c #[binder] .explicit
where
  c (ids : Array Syntax) (k : BinderKind) : BinderKind :=
    if ids.all (·.getKind == ``Parser.Term.hole) then
      .instance
    else
      k

private structure BinderWithDependents where
  idx : Nat
  kind : BinderKind
  binder : TSyntax binderKinds
  type? : Option Syntax
  default? : Option Syntax
  dependents : Array (Std.HashSet Nat)
deriving BEq, Inhabited

private def splitBinder (binder : TSyntax binderKinds)
    : Array Name × Option Syntax × Option Syntax :=
  if binder.raw.isIdent then
    (#[binder.raw.getId], none, none)
  else
    match binder.raw with
    | `(explicitBinderF| ($ids* $[: $type?:term]? $[$default?]?)) =>
      (binderIdentNames ids, type?.map (·.raw), default?.map (·.raw))
    | `(implicitBinderF| {$ids* $[: $type?:term]?})
    | `(strictImplicitBinderF| { {$ids* $[: $type?:term]?} })
    | `(strictImplicitBinderF| { {$ids* $[: $type?:term]?⦄)
    | `(strictImplicitBinderF| ⦃$ids* $[: $type?:term]?} })
    | `(strictImplicitBinderF| ⦃$ids* $[: $type?:term]?⦄) =>
      (binderIdentNames ids, type?.map (·.raw), none)
    | `(Parser.Term.instBinder| [$[$id?:ident :]? $classType:term]) =>
      (id?.toArray.map (·.getId), some classType.raw, none)
    | _ =>
      (#[], none, none)
where
  binderIdentNames (ids : Array Syntax) : Array Name :=
    ids.filterMap fun id => if id.isIdent then some id.getId else none

private partial def referencesVar (var : Name) : Syntax → Bool
  | .ident _ _ id _ => var.isPrefixOf id
  | .node _ _ args => args.any (referencesVar var)
  | _ => false

private def computeBinderDependents (binders : TSyntaxArray binderKinds)
    : Array BinderWithDependents := Id.run do
  let splitBinders := binders.map splitBinder
  let mut result := Array.emptyWithCapacity binders.size
  for i in 0...binders.size do
    let (boundVars, type?, default?) := splitBinders[i]!
    let mut dependents := #[]
    for bv in boundVars do
      let mut bvDependents := {}
      for j in (i + 1)...binders.size do
        let (_, body?, _) := splitBinders[j]!
        if body?.any (referencesVar bv) then
          bvDependents := bvDependents.insert j
      dependents := dependents.push bvDependents
    result := result.push ⟨i, .classify binders[i]!, binders[i]!, type?, default?, dependents⟩
  return result

private def hashPreresolved : Syntax.Preresolved → UInt64
  | .namespace ns => mixHash 11 (hash ns)
  | .decl n fields => mixHash 13 (mixHash (hash n) (hash fields))

/--
Hashes the same fields that `Syntax.structEq` compares, so it is consistent with `BEq Syntax`.
-/
private partial def hashSyntax : Syntax → UInt64
  | .missing =>
    17
  | .node _ k args =>
    args.foldl (fun r a => mixHash r (hashSyntax a)) (mixHash 19 (hash k))
  | .atom _ val =>
    mixHash 23 (hash val)
  | .ident _ rawVal val preresolved =>
    let h := mixHash 29 (hash rawVal.repair.toString)
    let h := mixHash h (hash val)
    preresolved.foldl (fun r p => mixHash r (hashPreresolved p)) h

private instance : Hashable Syntax := ⟨hashSyntax⟩

private structure PendingBinderGroup where
  binders : Array BinderWithDependents
  kinds : Std.HashSet BinderKind
  dependents : Std.HashSet Nat
  defaultKinds : Std.HashSet Bool
  types : Std.HashSet Syntax
deriving Inhabited

private def PendingBinderGroup.empty : PendingBinderGroup := {
  binders := #[]
  kinds := ∅
  dependents := ∅
  defaultKinds := ∅
  types := ∅
}

private def PendingBinderGroup.init (b : BinderWithDependents) : PendingBinderGroup := {
  binders := #[b]
  kinds := {b.kind}
  dependents := b.dependents.foldr Std.HashSet.union {}
  defaultKinds := {b.default?.isSome}
  types := b.type?.map ({·}) |>.getD {}
}

private def PendingBinderGroup.merge (g1 g2 : PendingBinderGroup) : PendingBinderGroup := {
  binders := g1.binders ++ g2.binders
  kinds := g1.kinds.union g2.kinds
  dependents := g1.dependents.union g2.dependents
  defaultKinds := g1.defaultKinds.union g2.defaultKinds
  types := g1.types.union g2.types
}

private def PendingBinderGroup.reverse (g : PendingBinderGroup) : PendingBinderGroup := {
  g with
  binders := g.binders.reverse
}

public def groupBinders (binders : TSyntaxArray binderKinds) : BinderGroups := Id.run do
  if binders.isEmpty then
    return #[]
  let binders := computeBinderDependents binders
  let mut runs := computeKindRuns binders |>.map (·.map PendingBinderGroup.init)
  runs :=
    runs.map fun run => Id.run do
      let mut groups := run
      groups := groupAdjacentImplicitsAndInstances groups
      groups := groupAdjacentByDependencyChain groups
      groups := groupAdjacentBinderlessExplicits groups
      groups := groupAdjacentExplicitsBySameType groups
      return groups
  let mut n := 0
  repeat do
    let n' := runs.map (·.size) |>.sum
    if n == n' then
      break
    n := n'
    let binderToGroup : Std.HashMap Nat Nat :=
      runs.flatMap id
        |>.mapIdx (fun groupIdx group => group.binders.map (·.idx, groupIdx))
        |>.flatMap id
        |> Std.HashMap.ofArray
    runs :=
      runs.map fun groups =>
        let groups := groupAdjacentExplicitsWithSameDependents binderToGroup groups
        let groups := groupAdjacentByCohesion groups
        groups
  let runs' := runs.map (·.map (·.binders))
  let runs' := runs'.map divideIntoSubgroups
  return runs'.flatMap (·.map (·.map (·.map (·.binder))))
where
  computeKindRuns (binders : Array BinderWithDependents)
      : Array (Array BinderWithDependents) := Id.run do
    let mut kindRuns := #[]
    let mut activeRun := #[binders[0]!]
    for b in binders[1...*] do
      match activeRun.back!.kind, b.kind with
      | .implicit, .implicit
      | .implicit, .explicit
      | .implicit, .instance
      | .explicit, .explicit
      | .explicit, .instance
      | .instance, .instance =>
        activeRun := activeRun.push b
      | _, _ =>
        kindRuns := kindRuns.push activeRun
        activeRun := #[b]
    kindRuns := kindRuns.push activeRun
    return kindRuns
  groupAdjacentByDependencyChain (groups : Array PendingBinderGroup)
      : Array PendingBinderGroup := Id.run do
    let mut chains : Array PendingBinderGroup := #[]
    let mut activeChain : PendingBinderGroup := groups[0]!
    for g in groups[1...*] do
      if g.binders.any (fun b => activeChain.dependents.contains b.idx) then
        activeChain := activeChain.merge g
      else
        chains := chains.push activeChain
        activeChain := g
    chains := chains.push activeChain

    chains := chains.reverse
    let mut chains' : Array PendingBinderGroup := #[]
    activeChain := chains[0]!
    let mut activeInitialAnchor : Array PendingBinderGroup := #[]
    for c in chains[1...*] do
      if c.binders.size = 1 && activeChain.binders.any (c.dependents.contains ·.idx) then
        activeInitialAnchor := activeInitialAnchor.push c
      else
        chains' :=
          chains'.push <|
            (activeInitialAnchor.reverse.push activeChain).foldl (init := .empty) (·.merge ·)
        activeInitialAnchor := #[]
        activeChain := c
    chains' :=
      chains'.push <|
        (activeInitialAnchor.reverse.push activeChain).foldl (init := .empty) (·.merge ·)
    chains' := chains'.reverse

    return chains'

  groupAdjacentImplicitsAndInstances (groups : Array PendingBinderGroup)
      : Array PendingBinderGroup := Id.run do
    let mut groupedGroups : Array PendingBinderGroup := #[]
    let mut activeGroup : PendingBinderGroup := groups[0]!
    for g in groups[1...*] do
      let isImplicitsOrInstances :=
        ! activeGroup.kinds.contains .explicit && ! g.kinds.contains .explicit
      if isImplicitsOrInstances then
        activeGroup := activeGroup.merge g
      else
        groupedGroups := groupedGroups.push activeGroup
        activeGroup := g
    groupedGroups := groupedGroups.push activeGroup
    return groupedGroups
  groupAdjacentBinderlessExplicits (groups : Array PendingBinderGroup)
      : Array PendingBinderGroup := Id.run do
    let mut groupedGroups : Array PendingBinderGroup := #[]
    let mut activeGroup : PendingBinderGroup := groups[0]!
    for g in groups[1...*] do
      let isExplicits := activeGroup.kinds == {.explicit} && g.kinds == {.explicit}
      let isBinderless := activeGroup.types.isEmpty && g.types.isEmpty
      if isExplicits && isBinderless && activeGroup.defaultKinds == g.defaultKinds then
        activeGroup := activeGroup.merge g
      else
        groupedGroups := groupedGroups.push activeGroup
        activeGroup := g
    groupedGroups := groupedGroups.push activeGroup
    return groupedGroups
  groupAdjacentExplicitsBySameType (groups : Array PendingBinderGroup)
      : Array PendingBinderGroup := Id.run do
    let mut groupedGroups : Array PendingBinderGroup := #[]
    let mut activeGroup : PendingBinderGroup := groups[0]!
    for g in groups[1...*] do
      let isExplicits := activeGroup.kinds == {.explicit} && g.kinds == {.explicit}
      let sameType : Bool := activeGroup.types.size == 1 && activeGroup.types == g.types
      if isExplicits && sameType && activeGroup.defaultKinds == g.defaultKinds then
        activeGroup := activeGroup.merge g
      else
        groupedGroups := groupedGroups.push activeGroup
        activeGroup := g
    groupedGroups := groupedGroups.push activeGroup
    return groupedGroups
  groupAdjacentExplicitsWithSameDependents
      (binderToGroup : Std.HashMap Nat Nat) (groups : Array PendingBinderGroup)
      : Array PendingBinderGroup := Id.run do
    let groupDependents (g : PendingBinderGroup) : Std.HashSet Nat :=
      g.dependents.toArray.map binderToGroup.get! |> Std.HashSet.ofArray
    let mut groupedGroups : Array PendingBinderGroup := #[]
    let mut activeGroup? : Option PendingBinderGroup := none
    for g in groups do
      match activeGroup? with
      | none =>
        let groupDeps :=
          g.binders.flatMap (·.dependents.map (·.toArray.map binderToGroup.get!
            |> Std.HashSet.ofArray))
        let hasSameGroupDeps := groupDeps.all (· == groupDeps[0]!)
        if hasSameGroupDeps && g.kinds == {.explicit} then
          activeGroup? := g
        else
          groupedGroups := groupedGroups.push g
      | some activeGroup =>
        let groupDeps :=
          g.binders.flatMap (·.dependents.map (·.toArray.map binderToGroup.get!
            |> Std.HashSet.ofArray))
        let hasSameGroupDeps := groupDeps.all (· == groupDeps[0]!)
        if hasSameGroupDeps && g.kinds == {.explicit} then
          if groupDependents g == groupDependents activeGroup
            && g.defaultKinds == activeGroup.defaultKinds
          then
            activeGroup? := activeGroup.merge g
          else
            groupedGroups := groupedGroups.push activeGroup
            activeGroup? := g
        else
          groupedGroups := groupedGroups.push activeGroup
          groupedGroups := groupedGroups.push g
          activeGroup? := none
    if let some activeGroup := activeGroup? then
      groupedGroups := groupedGroups.push activeGroup
    return groupedGroups
  groupAdjacentByCohesion (groups : Array PendingBinderGroup)
      : Array PendingBinderGroup := Id.run do
    let mut groupedGroups : Array PendingBinderGroup := #[]
    let mut activeGroup : PendingBinderGroup := groups[0]!
    for g in groups[1...*] do
      if g.binders.all (fun b => activeGroup.binders.any (·.dependents.any (·.contains b.idx)))
        && activeGroup.binders.all (fun b =>
          b.dependents.all (fun deps => g.binders.any (deps.contains ·.idx)))
      then
        activeGroup := activeGroup.merge g
      else
        groupedGroups := groupedGroups.push activeGroup
        activeGroup := g
    groupedGroups := groupedGroups.push activeGroup
    return groupedGroups
  divideIntoSubgroups (groups : Array (Array BinderWithDependents))
      : Array (Array (Array BinderWithDependents)) :=
    groups.map fun group => Id.run do
      let mut dividedGroups : Array (Array BinderWithDependents) := #[]
      let mut activeGroup : Array BinderWithDependents := #[group[0]!]
      for b in group[1...*] do
        match activeGroup.back!.kind, b.kind with
        | .implicit, .implicit
        | .instance, .instance =>
          activeGroup := activeGroup.push b
        | .explicit, .explicit =>
          if activeGroup.back!.default?.isSome == b.default?.isSome then
            activeGroup := activeGroup.push b
          else
            dividedGroups := dividedGroups.push activeGroup
            activeGroup := #[b]
        | _, _ =>
          dividedGroups := dividedGroups.push activeGroup
          activeGroup := #[b]
      dividedGroups := dividedGroups.push activeGroup

      if dividedGroups.size > 1 then
        return dividedGroups

      let mut dividedGroups' : Array (Array BinderWithDependents) := #[]
      for group in dividedGroups do
        let mut i : Int := 0
        while i < group.size do
          let b := group[i.toNat]!
          if group[0...i.toNat].any (fun p => p.dependents.any (·.contains b.idx)) then
            break
          i := i + 1
        if i <= 1 then
          i := 0
        let mut j : Int := group.size - 1
        while j >= i do
          let b := group[j.toNat]!
          if group[(j + 1).toNat...*].any (fun p => b.dependents.any (·.contains p.idx)) then
            break
          j := j - 1
        if j >= group.size - 2 then
          j := group.size - 1
        let pre := group[0...i.toNat]
        let mid := group[i.toNat...(j + 1).toNat]
        let post := group[(j + 1).toNat...*]
        if pre.size > 0 then
          dividedGroups' := dividedGroups'.push pre
        if mid.size > 0 then
          dividedGroups' := dividedGroups'.push mid
        if post.size > 0 then
          dividedGroups' := dividedGroups'.push post
      return dividedGroups'

public def fmtBinders (binders : TSyntaxArray binderKinds)
    : FmtM (Array (Array (Array TaggedDoc))) := do
  let binderGroups := groupBinders binders
  let binderGroups ←
    binderGroups.mapM fun binderGroup =>
      binderGroup.mapM fun subBinderGroup => subBinderGroup.mapM fmt
  return binderGroups

public def fmtBinder
    (lbTks : Array Syntax) (lhses : Array Syntax) (subBinders : TSyntaxArray binderKinds)
    (typeAscriptionTk? : Option Syntax) (type? : Option (TSyntax `term))
    (tacticOrDefault? : Option (TSyntax [``Parser.Term.binderTactic, ``Parser.Term.binderDefault]))
    (rbTks : Array Syntax)
    (kind : Layouts.Types.SignatureKind :=
      Layouts.Types.SignatureKind.local (respectPseudoAlignment := false))
    : FmtM TaggedDoc := do
  let lbTks ← lbTks.mapM fmt
  let lhses ← lhses.mapM fmt
  let subBinderGroups ← fmtBinders subBinders
  let typeAscriptionTk? ← fmt? typeAscriptionTk?
  let type? ← fmt? type?
  let (colonEqTk?, default?) :=
    Option.split <| ← tacticOrDefault?.mapM fun
      | `(Parser.Term.binderTactic| :=%$colonEqTk by%$byTk $tacticSeq) => do
        let colonEqTk ← fmt colonEqTk
        let byTk ← fmt byTk
        let tacticSeq ← fmt tacticSeq
        return (colonEqTk, Layouts.keywordPrefixedSeq byTk tacticSeq .sticky)
      | `(Parser.Term.binderDefault| :=%$colonEqTk $term) => do
        let colonEqTk ← fmt colonEqTk
        let term ← fmt term
        return (colonEqTk, term)
      | _ =>
        throw .partialFormatter
  let colonEqTk? := colonEqTk?.getD empty
  let default? := default?.getD empty
  let rbTks ← rbTks.mapM fmt
  return Layouts.binder lbTks lhses subBinderGroups typeAscriptionTk? type? colonEqTk? default?
    rbTks kind

public def fmtLocalSignature
    (lval : Syntax) (binders : TSyntaxArray binderKinds) (typeAscriptionTk? : Option Syntax)
    (type? : Option Syntax)
    : FmtM TaggedDoc := do
  let lval ← fmt lval
  let binders ← fmtBinders binders
  let typeAscriptionTk? ← fmt? typeAscriptionTk?
  let type? ← fmt? type?
  return Layouts.localSignature #[lval] binders typeAscriptionTk? type?

public def fmtGlobalSignature
    (lval : Syntax) (binders : TSyntaxArray binderKinds) (typeAscriptionTk? : Option Syntax)
    (type? : Option Syntax)
    : FmtM TaggedDoc := do
  let lval ← fmt lval
  let binders ← fmtBinders binders
  let typeAscriptionTk? ← fmt? typeAscriptionTk?
  let type? ← fmt? type?
  return Layouts.globalSignature #[lval] binders typeAscriptionTk? type?

public def fmtNamedArgumentTerm
    (lbTk : Syntax) (lhs : Syntax) (colonEqTk : Syntax) (body : Syntax) (rbTk : Syntax)
    : FmtM TaggedDoc := do
  let lbTk ← fmt lbTk
  let lhs ← fmt lhs
  let colonEqTk ← fmt colonEqTk
  let body ← fmt body
  let rbTk ← fmt rbTk
  return Layouts.binder #[lbTk] #[lhs] #[] empty empty colonEqTk body #[rbTk]
    (kind := .local (respectPseudoAlignment := true))

public def fmtNamedArgumentTerm?
    (lbTk? : Option Syntax) (lhs? : Option Syntax) (colonEqTk? : Option Syntax)
    (body? : Option Syntax) (rbTk? : Option Syntax)
    : FmtM TaggedDoc := do
  let (some lbTk, some lhs, some colonEqTk, some body, some rbTk) :=
      (lbTk?, lhs?, colonEqTk?, body?, rbTk?)
    | return empty
  fmtNamedArgumentTerm lbTk lhs colonEqTk body rbTk

/--
Turns the alternatives of a `| pats | pats | pats => rhs` left-hand side into one sub-alternative
per `|`, attaching each `|` to the alternative that follows it.
-/
public def joinAltPats (initialAltTk : TaggedDoc) (patss : SepArray sep)
    : Array TaggedDoc := Id.run do
  let mut r := #[initialAltTk]
  for i in (0...patss.elemsAndSeps.size) do
    let patsOrSep := patss.elemsAndSeps[i]!
    if i % 2 == 0 then
      r :=
        r.modify (r.size - 1) fun lastAltTk =>
          nested <| Layouts.spacedAtomic #[lastAltTk, patsOrSep]
    else
      r := r.push patsOrSep
  return r

public def fmtTermInstruction
    (instruction : TaggedDoc) (instructionComponents : Array Syntax) (semicolonTk? : Option Syntax)
    (body : Syntax)
    : FmtM TaggedDoc := do
  let instructionTrailing ←
    fmtTrailingWithRetainedNewlinesAndComments (atleastOneNewline := false) <| mkNullNode <|
      instructionComponents ++ semicolonTk?.toArray
  let semicolonTk? ← fmt? semicolonTk?
  let body ← fmt body
  if !instructionTrailing.isAlwaysEmpty then
    return withPosition <| Layouts.retainedWhitespace #[instruction, instructionTrailing, body]
  let singleLineAlt := flattened <| combine #[instruction, semicolonTk?, .withSepBefore body space]
  let multiLineAlt := Layouts.lines #[instruction, body]
  return withPosition <| oneOf #[singleLineAlt, multiLineAlt]

public def isAttributesSimple? : TSyntax ``Parser.Term.attributes → Option Bool
  | `(Parser.Term.attributes| @[ $attrInstances:attrInstance,* ]) =>
    attrInstances.getElems.allM fun
      | `(Parser.Term.attrInstance| $_:attrKind $attr:attr) => do
        let mut numLeafs := 0
        for node in attr.raw.topDown do
          if node.isIdent || node.isAtom then
            numLeafs := numLeafs + 1
          if numLeafs > 1 then
            return false
        return true
      | _ =>
        none
  | _ =>
    none

public def fmtDeclWithAttributes
    (attributes? : Option (TSyntax ``Parser.Term.attributes)) (decl : TaggedDoc)
    (compact : Bool := false)
    : FmtM TaggedDoc := do
  let isAttributesSimple := attributes?.any (isAttributesSimple? · |>.getD false)
  let attributes? ← fmt? attributes?
  if isAttributesSimple then
    if compact then
      return Layouts.softSpacedAtomic #[attributes?, decl]
    else
      return Layouts.horizontalOrVertical #[attributes?, decl]
  else
    return Layouts.lines #[attributes?, decl]

public def fmtDeclWithModifiers
    (docComment? : Option (TSyntax ``Parser.Command.docComment))
    (attributes? : Option (TSyntax ``Parser.Term.attributes)) (mods : Array (Option Syntax))
    (decl : TaggedDoc)
    : FmtM TaggedDoc := do
  let docComment? ← fmt? docComment?
  let mods ← mods.filterMap id |>.mapM fmt
  let mods := Layouts.spacedAtomic mods
  let fullDecl := Layouts.spacedAtomic #[mods, decl]
  let declWithAttributes ← fmtDeclWithAttributes attributes? fullDecl
  return Layouts.lines #[docComment?, declWithAttributes]

public def fmtDeclWithDeclModifiers
    (declModifiers : TSyntax ``Parser.Command.declModifiers) (decl : TaggedDoc)
    : FmtM TaggedDoc := do
  let `(declModifiers|
      $[$docComment?:docComment]?
      $[$attributes?:attributes]?
      $[$visibility?:visibility]?
      $[$protected?:protected]?
      $[$metaOrNoncomputable?]?
      $[$unsafe?:unsafe]?
      $[$partialOrNonrec?]?) :=
      declModifiers
    | throw .partialFormatter
  fmtDeclWithModifiers docComment? attributes?
    #[visibility?, protected?, metaOrNoncomputable?, unsafe?, partialOrNonrec?] decl

public def fmtDeclarationSignature
    (declTks : Array Syntax) (namedPrio? : Option Syntax) (declId? : Option Syntax)
    (binders : TSyntaxArray [`ident, ``Parser.Term.hole, ``Parser.Term.bracketedBinder])
    (typeAscriptionTk? : Option Syntax) (type? : Option Syntax)
    : FmtM TaggedDoc := do
  let declTks := Layouts.spacedAtomic (← declTks.mapM fmt)
  let namedPrio? ← fmt? namedPrio?
  let lvalLhs := Layouts.pseudoApplication #[declTks, namedPrio?]
  let declId? ← fmt? declId?
  let binders ← fmtBinders binders
  let typeAscriptionTk? ← fmt? typeAscriptionTk?
  let type? ← fmt? type?
  return Layouts.globalSignature #[lvalLhs, declId?] binders typeAscriptionTk? type?

public def fmtAssignmentDeclaration
    (declTk : Syntax) (namedPrio? : Option Syntax) (declId? : Option Syntax)
    (binders : TSyntaxArray [`ident, ``Parser.Term.hole, ``Parser.Term.bracketedBinder])
    (typeAscriptionTk? : Option Syntax) (type? : Option Syntax) (colonEqTk? : Option Syntax)
    (declBody : Syntax) (terminationSuffix? : Option (TSyntax ``Parser.Termination.suffix))
    (whereDecls? : Option (TSyntax ``Parser.Term.whereDecls))
    : FmtM TaggedDoc := do
  let signatureDoc ←
    fmtDeclarationSignature #[declTk] namedPrio? declId? binders typeAscriptionTk? type?
  let colonEqTkDoc? ← fmt? colonEqTk?
  let declBodyDoc ← fmt declBody
  let mainDeclDoc := Layouts.assignmentDeclaration signatureDoc colonEqTkDoc? declBodyDoc
  let mainDeclTrailingDoc ← fmtTrailingWithRetainedNewlinesAndComments declBody
  let terminationSuffixDoc ← fmt? terminationSuffix?
  let terminationSuffixTrailingDoc :=
    (← terminationSuffix?.mapM fmtTrailingWithRetainedNewlinesAndComments).getD empty
  let whereDecls? ← fmt? whereDecls?
  return Layouts.retainedWhitespace #[
    mainDeclDoc,
    mainDeclTrailingDoc,
    terminationSuffixDoc,
    terminationSuffixTrailingDoc,
    whereDecls?
  ]

public def fmtMatchDeclaration
    (declTk : Syntax) (namedPrio? : Option Syntax) (declId? : Option Syntax)
    (binders : TSyntaxArray [`ident, ``Parser.Term.hole, ``Parser.Term.bracketedBinder])
    (typeAscriptionTk? : Option Syntax) (type? : Option Syntax)
    (matchAlts : TSyntax ``Parser.Term.matchAlts)
    (terminationSuffix? : Option (TSyntax ``Parser.Termination.suffix))
    (whereDecls? : Option (TSyntax ``Parser.Term.whereDecls))
    : FmtM TaggedDoc := do
  let signatureDoc ←
    fmtDeclarationSignature #[declTk] namedPrio? declId? binders typeAscriptionTk? type?
  let matchAltsDoc ← fmt matchAlts
  let mainDeclDoc := Layouts.matchDeclaration signatureDoc matchAltsDoc
  let mainDeclTrailingDoc ← fmtTrailingWithRetainedNewlinesAndComments matchAlts
  let terminationSuffixDoc ← fmt? terminationSuffix?
  let terminationSuffixTrailingDoc :=
    (← terminationSuffix?.mapM fmtTrailingWithRetainedNewlinesAndComments).getD empty
  let whereDecls? ← fmt? whereDecls?
  return Layouts.retainedWhitespace #[
    mainDeclDoc,
    mainDeclTrailingDoc,
    terminationSuffixDoc,
    terminationSuffixTrailingDoc,
    whereDecls?
  ]

public def fmtWhereDeclaration
    (declTk : Syntax) (namedPrio? : Option Syntax) (declId? : Option Syntax)
    (binders : TSyntaxArray [`ident, ``Parser.Term.hole, ``Parser.Term.bracketedBinder])
    (typeAscriptionTk? : Option Syntax) (type? : Option Syntax) (whereTk : Syntax)
    (fields : Syntax.TSepArray ``Parser.Term.structInstField ";")
    (whereDecls? : Option (TSyntax ``Parser.Term.whereDecls))
    : FmtM TaggedDoc := do
  let signature ←
    fmtDeclarationSignature #[declTk] namedPrio? declId? binders typeAscriptionTk? type?
  let «where» ← fmt whereTk
  let fieldsDoc ← fmtTSepArray fields
  let mainDeclTrailingDoc ←
    fmtTrailingWithRetainedNewlinesAndComments <| mkNullNode <| #[whereTk] ++ fields
  let whereDecls? ← fmt? whereDecls?
  let fields := Layouts.sepLines fieldsDoc (includeSeps := false)
  let mainDecl := Layouts.whereDeclaration signature «where» fields
  return Layouts.retainedWhitespace #[
    mainDecl,
    mainDeclTrailingDoc,
    whereDecls?
  ]

public def fmtInductiveLike
    (tks : Array Syntax) (declId : TSyntax ``Parser.Command.declId)
    (binders : TSyntaxArray [`ident, ``Parser.Term.hole, ``Parser.Term.bracketedBinder])
    (typeAscriptionTk? : Option Syntax) (type? : Option (TSyntax `term)) (sepTk? : Option Syntax)
    (ctors : TSyntaxArray ``Parser.Command.ctor)
    (computedFields? : Option (TSyntax ``Parser.Command.computedFields))
    (optDeriving : TSyntax ``Parser.Command.optDeriving)
    (monotonicityBy? : Option (TSyntax ``Parser.Command.monotonicityBy))
    : FmtM TaggedDoc := do
  let signatureDoc ← fmtDeclarationSignature tks none declId binders typeAscriptionTk? type?
  let sepTkDoc? ← fmt? sepTk?
  let ctorsDoc ← fmtArray ctors
  let ctorsDoc := Layouts.lines ctorsDoc
  let mainDeclDoc := Layouts.whereDeclaration signatureDoc sepTkDoc? ctorsDoc
  let optDerivingDoc ← fmt optDeriving
  let monotonicityByDoc? ← fmt? monotonicityBy?
  match computedFields? with
  | none =>
    return Layouts.lines #[mainDeclDoc, optDerivingDoc, monotonicityByDoc?]
  | some computedFields =>
    let mainDeclTrailingDoc ←
      fmtTrailingWithRetainedNewlinesAndComments <| mkNullNode <|
        tks ++ #[declId] ++ binders ++ typeAscriptionTk?.toArray ++ type?.toArray ++ sepTk?.toArray
          ++ ctors
    let computedFieldsDoc ← fmt computedFields
    let computedFieldsTrailingDoc ← fmtTrailingWithRetainedNewlinesAndComments computedFields
    let optDerivingTrailingDoc ← fmtTrailingWithRetainedNewlinesAndComments optDeriving
    return Layouts.retainedWhitespace #[
      mainDeclDoc,
      mainDeclTrailingDoc,
      computedFieldsDoc,
      computedFieldsTrailingDoc,
      optDerivingDoc,
      optDerivingTrailingDoc,
      monotonicityByDoc?
    ]

public def fmtStructureLike
    (tk : Syntax) (declId : TSyntax ``Parser.Command.declId)
    (binders : TSyntaxArray [`ident, ``Parser.Term.hole, ``Parser.Term.bracketedBinder])
    (typeAscriptionTk? : Option Syntax) (type? : Option (TSyntax `term))
    (extends? : Option (TSyntax ``Parser.Command.extends)) (sepTk? : Option Syntax)
    (structCtor? : Option (TSyntax ``Parser.Command.structCtor))
    (structFields? : Option (Array Syntax)) (optDeriving : TSyntax ``Parser.Command.optDeriving)
    : FmtM TaggedDoc := do
  let signature ← fmtDeclarationSignature #[tk] none declId binders typeAscriptionTk? type?
  let (extendsTk?, structParents?) :=
    Option.split <| ← extends?.mapM fun
      | `(Parser.Command.extends| extends%$extendsTk $structParents:structParent,*) => do
        let extendsTk ← fmt extendsTk
        let structParents ← fmtSepArray (sep := ",") structParents
        return (extendsTk, structParents)
      | _ =>
        throw .partialFormatter
  let extendsTk? := extendsTk?.getD empty
  let structParents? := structParents?.getD ⟨#[]⟩
  let sepTk? ← fmt? sepTk?
  let structCtor? ← fmt? structCtor?
  let structFields ← structFields?.getD #[] |>.mapM fmt
  let optDeriving ← fmt optDeriving
  let «extends» := Layouts.keywordPrefixedSepFill extendsTk? structParents? .nonSticky
  let extendedSignature :=
    Layouts.blocks #[{ block := signature, hardNestedIfFirst := false }, «extends»]
  let structFields := Layouts.lines structFields
  let structBody := Layouts.lines #[structCtor?, structFields]
  let mainDecl := Layouts.whereDeclaration extendedSignature sepTk? structBody
  return Layouts.lines #[mainDecl, optDeriving]

public def fmtAltsTactic (kwTk : Syntax) (barTks : Array Syntax) (cases : Array (TSyntax k))
    : FmtM TaggedDoc := do
  let kwTk ← fmt kwTk
  let cases ←
    barTks.zip cases
      |>.mapM fun (barTk, tacticSeq) => do
        let barTk ← fmt barTk
        let tacticSeq ← fmt tacticSeq
        return .withSepAfter (nested <| Layouts.softSpacedAtomic #[barTk, tacticSeq]) nl
  let cases := withPosition <| combine cases
  return Layouts.horizontalOrVertical #[kwTk, cases]

public def tacticOptConfigItems (stx : TSyntax ``Parser.Tactic.optConfig)
    : FmtM (Array Syntax) := do
  match stx with
  | `(Parser.Tactic.optConfig| $items:configItem*) => return items
  | _ => throw .partialFormatter

public def fmtSimpLikeWithGenericConfig
    (lhs : Array Syntax) (cfgItems : Array Syntax)
    (disch? : Option (TSyntax ``Parser.Tactic.discharger)) (only? : Option Syntax)
    (lbTk? : Option Syntax) (args? : Option (Syntax.SepArray ",")) (rbTk? : Option Syntax)
    (suffix? : Option (TSyntax ``Parser.Tactic.location))
    : FmtM TaggedDoc := do
  let lhs := Layouts.spacedAtomic (← lhs.mapM fmt)
  let cfgItems ← cfgItems.mapM fmt
  let disch? ← fmt? disch?
  let «simp» := Layouts.pseudoApplication <| #[lhs] ++ cfgItems ++ #[disch?]
  let onlyTk? ← fmt? only?
  let lbTk? ← fmt? lbTk?
  let args ← fmtSepArray (args?.getD ⟨#[]⟩)
  let rbTk? ← fmt? rbTk?
  let suffix? ← fmt? suffix?
  let args := Layouts.keywordPrefixedCollection onlyTk? lbTk? args rbTk?
  return Layouts.blocks #[«simp», args, suffix?]

public def fmtSimpLike
    (lhs : Array Syntax) (cfg : TSyntax ``Parser.Tactic.optConfig)
    (disch? : Option (TSyntax ``Parser.Tactic.discharger)) (only? : Option Syntax)
    (lbTk? : Option Syntax) (args? : Option (Syntax.SepArray ",")) (rbTk? : Option Syntax)
    (suffix? : Option (TSyntax ``Parser.Tactic.location))
    : FmtM TaggedDoc := do
  let `(Parser.Tactic.optConfig| $cfgItems:configItem*) := cfg
    | throw .partialFormatter
  fmtSimpLikeWithGenericConfig lhs cfgItems disch? only? lbTk? args? rbTk? suffix?

public def fmtRwLike
    (rwTk : Syntax) (cfg? : Option (TSyntax ``Parser.Tactic.optConfig)) (rules : Syntax)
    (loc? : Option (TSyntax `Lean.Parser.Tactic.location))
    : FmtM TaggedDoc := do
  let cfg := (← cfg?.mapM tacticOptConfigItems).getD #[]
  let rwTk ← fmt rwTk
  let cfg ← cfg.mapM fmt
  let «rw» := Layouts.pseudoApplication <| #[rwTk] ++ cfg
  let rules ← fmt rules
  let loc? ← fmt? loc?
  return Layouts.blocks #[«rw», rules, loc?]

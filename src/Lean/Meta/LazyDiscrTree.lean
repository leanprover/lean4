/-
Copyright (c) 2023 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joe Hendrix, Kim Morrison
-/
prelude
import Lean.Meta.CompletionName
import Lean.Meta.DiscrTree

/-!
# Lazy Discrimination Tree

This file defines a new type of discrimination tree optimized for rapid
population of imported modules for use in tactics.  It uses a lazy
initialization strategy.

The discrimination tree can be created through
`createImportedEnvironment`. This creates a discrimination tree from all
imported modules in an environment using a callback that provides the
entries as `InitEntry` values.

The function `getMatch` can be used to get the values that match the
expression as well as an updated lazy discrimination tree that has
elaborated additional parts of the tree.
-/
namespace Lean.Meta.LazyDiscrTree

/--
Discrimination tree key.
-/
inductive Key where
  | const : Name → Nat → Key
  | fvar  : FVarId → Nat → Key
  | lit   : Literal → Key
  | star  : Key
  | other : Key
  | arrow : Key
  | proj  : Name → Nat → Nat → Key
  deriving Inhabited, BEq, Repr

namespace Key

/-- Hash function -/
protected def hash : Key → UInt64
  | .const n a   => mixHash 5237 $ mixHash n.hash (hash a)
  | .fvar n a    => mixHash 3541 $ mixHash (hash n) (hash a)
  | .lit v       => mixHash 1879 $ hash v
  | .star        => 7883
  | .other       => 2411
  | .arrow       => 17
  | .proj s i a  =>  mixHash (hash a) $ mixHash (hash s) (hash i)

instance : Hashable Key := ⟨Key.hash⟩

end Key

-- This namespace contains definitions copied from Lean.Meta.DiscrTree.
namespace MatchClone

private def tmpMVarId : MVarId := { name := `_discr_tree_tmp }
private def tmpStar := mkMVar tmpMVarId

/--
  Returns true iff the argument should be treated as a "wildcard" by the
  discrimination tree.

  This includes proofs, instance implicit arguments, implicit arguments,
  and terms of the form `noIndexing t`

  This is a clone of `Lean.Meta.DiscrTree.ignoreArg` and mainly added to
  avoid coupling between `DiscrTree` and `LazyDiscrTree` while both are
  potentially subject to independent changes.
-/
private def ignoreArg (a : Expr) (i : Nat) (infos : Array ParamInfo) : MetaM Bool := do
  if h : i < infos.size then
    let info := infos[i]
    if info.isInstImplicit then
      return true
    else if info.isImplicit || info.isStrictImplicit then
      return !(← isType a)
    else
      isProof a
  else
    isProof a

private partial def pushArgsAux (infos : Array ParamInfo) : Nat → Expr → Array Expr → MetaM (Array Expr)
  | i, .app f a, todo => do
    if (← ignoreArg a i infos) then
      pushArgsAux infos (i-1) f (todo.push tmpStar)
    else
      pushArgsAux infos (i-1) f (todo.push a)
  | _, _, todo => return todo

/--
  Returns `true` if `e` is one of the following
  - A nat literal (numeral)
  - `Nat.zero`
  - `Nat.succ x` where `isNumeral x`
  - `OfNat.ofNat _ x _` where `isNumeral x` -/
private partial def isNumeral (e : Expr) : Bool :=
  if e.isRawNatLit then true
  else
    let f := e.getAppFn
    if !f.isConst then false
    else
      let fName := f.constName!
      if fName == ``Nat.succ && e.getAppNumArgs == 1 then isNumeral e.appArg!
      else if fName == ``OfNat.ofNat && e.getAppNumArgs == 3 then isNumeral (e.getArg! 1)
      else if fName == ``Nat.zero && e.getAppNumArgs == 0 then true
      else false

private partial def toNatLit? (e : Expr) : Option Literal :=
  if isNumeral e then
    if let some n := loop e then
      some (.natVal n)
    else
      none
  else
    none
where
  loop (e : Expr) : OptionT Id Nat := do
    let f := e.getAppFn
    match f with
    | .lit (.natVal n) => return n
    | .const fName .. =>
      if fName == ``Nat.succ && e.getAppNumArgs == 1 then
        let r ← loop e.appArg!
        return r+1
      else if fName == ``OfNat.ofNat && e.getAppNumArgs == 3 then
        loop (e.getArg! 1)
      else if fName == ``Nat.zero && e.getAppNumArgs == 0 then
        return 0
      else
        failure
    | _ => failure

private def isNatType (e : Expr) : MetaM Bool :=
  return (← whnf e).isConstOf ``Nat

/--
  Returns `true` if `e` is one of the following
  - `Nat.add _ k` where `isNumeral k`
  - `Add.add Nat _ _ k` where `isNumeral k`
  - `HAdd.hAdd _ Nat _ _ k` where `isNumeral k`
  - `Nat.succ _`
  This function assumes `e.isAppOf fName`
-/
private def isNatOffset (fName : Name) (e : Expr) : MetaM Bool := do
  if fName == ``Nat.add && e.getAppNumArgs == 2 then
    return isNumeral e.appArg!
  else if fName == ``Add.add && e.getAppNumArgs == 4 then
    if (← isNatType (e.getArg! 0)) then return isNumeral e.appArg! else return false
  else if fName == ``HAdd.hAdd && e.getAppNumArgs == 6 then
    if (← isNatType (e.getArg! 1)) then return isNumeral e.appArg! else return false
  else
    return fName == ``Nat.succ && e.getAppNumArgs == 1

/-
This is a hook to determine if we should add an expression as a wildcard pattern.

Clone of `Lean.Meta.DiscrTree.shouldAddAsStar`.  See it for more discussion.
-/
private def shouldAddAsStar (fName : Name) (e : Expr) : MetaM Bool := do
  isNatOffset fName e

/--
Eliminate loose bound variables via beta-reduction.

This is primarily used to reduce pi-terms `∀(x : P), T` into
non-dependend functions `P → T`.  The latter has a more specific
discrimination tree key `.arrow..` and this improves the accuracy of the
discrimination tree.

Clone of `Lean.Meta.DiscrTree.elimLooseBVarsByBeta`.  See it for more
discussion.
-/
private def elimLooseBVarsByBeta (e : Expr) : CoreM Expr :=
  Core.transform e
    (pre := fun e => do
      if !e.hasLooseBVars then
        return .done e
      else if e.isHeadBetaTarget then
        return .visit e.headBeta
      else
        return .continue)

private def getKeyArgs (e : Expr) (isMatch root : Bool) (config : WhnfCoreConfig) :
    MetaM (Key × Array Expr) := do
  let e ← DiscrTree.reduceDT e root config
  unless root do
    -- See pushArgs
    if let some v := toNatLit? e then
      return (.lit v, #[])
  match e.getAppFn with
  | .lit v         => return (.lit v, #[])
  | .const c _     =>
    if (← getConfig).isDefEqStuckEx && e.hasExprMVar then
      if (← isReducible c) then
        /- `e` is a term `c ...` s.t. `c` is reducible and `e` has metavariables, but it was not
            unfolded.  This can happen if the metavariables in `e` are "blocking" smart unfolding.
           If `isDefEqStuckEx` is enabled, then we must throw the `isDefEqStuck` exception to
           postpone TC resolution.
        -/
        Meta.throwIsDefEqStuck
      else if let some matcherInfo := isMatcherAppCore? (← getEnv) e then
        -- A matcher application is stuck if one of the discriminants has a metavariable
        let args := e.getAppArgs
        let start := matcherInfo.getFirstDiscrPos
        for arg in args[ start : start + matcherInfo.numDiscrs ] do
          if arg.hasExprMVar then
            Meta.throwIsDefEqStuck
      else if (← isRec c) then
        /- Similar to the previous case, but for `match` and recursor applications. It may be stuck
           (i.e., did not reduce) because of metavariables. -/
        Meta.throwIsDefEqStuck
    let nargs := e.getAppNumArgs
    return (.const c nargs, e.getAppRevArgs)
  | .fvar fvarId   =>
    let nargs := e.getAppNumArgs
    return (.fvar fvarId nargs, e.getAppRevArgs)
  | .mvar mvarId   =>
    if isMatch then
      return (.other, #[])
    else do
      let ctx ← read
      if ctx.config.isDefEqStuckEx then
        /-
          When the configuration flag `isDefEqStuckEx` is set to true,
          we want `isDefEq` to throw an exception whenever it tries to assign
          a read-only metavariable.
          This feature is useful for type class resolution where
          we may want to notify the caller that the TC problem may be solvable
          later after it assigns `?m`.
          The method `DiscrTree.getUnify e` returns candidates `c` that may "unify" with `e`.
          That is, `isDefEq c e` may return true. Now, consider `DiscrTree.getUnify d (Add ?m)`
          where `?m` is a read-only metavariable, and the discrimination tree contains the keys
          `HadAdd Nat` and `Add Int`. If `isDefEqStuckEx` is set to true, we must treat `?m` as
          a regular metavariable here, otherwise we return the empty set of candidates.
          This is incorrect because it is equivalent to saying that there is no solution even if
          the caller assigns `?m` and try again. -/
        return (.star, #[])
      else if (← mvarId.isReadOnlyOrSyntheticOpaque) then
        return (.other, #[])
      else
        return (.star, #[])
  | .proj s i a .. =>
    let nargs := e.getAppNumArgs
    return (.proj s i nargs, #[a] ++ e.getAppRevArgs)
  | .forallE _ d b _ =>
    -- See comment at elimLooseBVarsByBeta
    let b ← if b.hasLooseBVars then elimLooseBVarsByBeta b else pure b
    if b.hasLooseBVars then
      return (.other, #[])
    else
      return (.arrow, #[d, b])
  | .bvar _ | .letE _ _ _ _ _ | .lam _ _ _ _ | .mdata _ _ | .app _ _ | .sort _ =>
    return (.other, #[])

/-
Given an expression we are looking for patterns that match, return the key and sub-expressions.
-/
private abbrev getMatchKeyArgs (e : Expr) (root : Bool) (config : WhnfCoreConfig) :
    MetaM (Key × Array Expr) :=
  getKeyArgs e (isMatch := true) (root := root) (config := config)

end MatchClone

/--
An unprocessed entry in the lazy discrimination tree.
-/
private abbrev LazyEntry α := Array Expr × ((LocalContext × LocalInstances) × α)

/--
Index identifying trie in a discrimination tree.
-/
@[reducible]
private def TrieIndex := Nat

/--
Discrimination tree trie. See `LazyDiscrTree`.
-/
private structure Trie (α : Type) where
  node ::
    /-- Values for matches ending at this trie. -/
    values : Array α
    /-- Index of trie matching star. -/
    star : TrieIndex
    /-- Following matches based on key of trie. -/
    children : Std.HashMap Key TrieIndex
    /-- Lazy entries at this trie that are not processed. -/
    pending : Array (LazyEntry α) := #[]
  deriving Inhabited

instance : EmptyCollection (Trie α) := ⟨.node #[] 0 {} #[]⟩

/-- Push lazy entry to trie. -/
private def Trie.pushPending : Trie α → LazyEntry α → Trie α
| .node vs star cs p, e => .node vs star cs (p.push e)

end LazyDiscrTree

/--
`LazyDiscrTree` is a variant of the discriminator tree datatype
`DiscrTree` in Lean core that is designed to be efficiently
initializable with a large number of patterns.  This is useful
in contexts such as searching an entire Lean environment for
expressions that match a pattern.

Lazy discriminator trees achieve good performance by minimizing
the amount of work that is done up front to build the discriminator
tree.  When first adding patterns to the tree, only the root
discriminator key is computed and processing the remaining
terms is deferred until demanded by a match.
-/
structure LazyDiscrTree (α : Type) where
  /-- Configuration for normalization. -/
  config : Lean.Meta.WhnfCoreConfig := {}
  /-- Backing array of trie entries.  Should be owned by this trie. -/
  tries : Array (LazyDiscrTree.Trie α) := #[default]
  /-- Map from discriminator trie roots to the index. -/
  roots : Std.HashMap LazyDiscrTree.Key LazyDiscrTree.TrieIndex := {}

namespace LazyDiscrTree

open Lean Elab Meta

instance : Inhabited (LazyDiscrTree α) where
  default := {}

open Lean.Meta.DiscrTree (mkNoindexAnnotation hasNoindexAnnotation reduceDT)

/--
Specialization of Lean.Meta.DiscrTree.pushArgs
-/
private def pushArgs (root : Bool) (todo : Array Expr) (e : Expr) (config : WhnfCoreConfig) :
    MetaM (Key × Array Expr) := do
  if hasNoindexAnnotation e then
    return (.star, todo)
  else
    let e ← reduceDT e root config
    let fn := e.getAppFn
    let push (k : Key) (nargs : Nat) (todo : Array Expr) : MetaM (Key × Array Expr) := do
      let info ← getFunInfoNArgs fn nargs
      let todo ← MatchClone.pushArgsAux info.paramInfo (nargs-1) e todo
      return (k, todo)
    match fn with
    | .lit v     =>
      return (.lit v, todo)
    | .const c _ =>
      unless root do
        if let some v := MatchClone.toNatLit? e then
          return (.lit v, todo)
        if (← MatchClone.shouldAddAsStar c e) then
          return (.star, todo)
      let nargs := e.getAppNumArgs
      push (.const c nargs) nargs todo
    | .proj s i a =>
      /-
      If `s` is a class, then `a` is an instance. Thus, we annotate `a` with `no_index` since we do
      not index instances. This should only happen if users mark a class projection function as
      `[reducible]`.

      TODO: add better support for projections that are functions
      -/
      let a := if isClass (← getEnv) s then mkNoindexAnnotation a else a
      let nargs := e.getAppNumArgs
      push (.proj s i nargs) nargs (todo.push a)
    | .fvar _fvarId   =>
      return (.star, todo)
    | .mvar mvarId   =>
      if mvarId == MatchClone.tmpMVarId then
        -- We use `tmp to mark implicit arguments and proofs
        return (.star, todo)
      else
        failure
    | .forallE _ d b _ =>
      -- See comment at elimLooseBVarsByBeta
      let b ← if b.hasLooseBVars then MatchClone.elimLooseBVarsByBeta b else pure b
      if b.hasLooseBVars then
        return (.other, todo)
      else
        return (.arrow, (todo.push d).push b)
    | _ =>
      return (.other, todo)

/-- Initial capacity for key and todo vector. -/
private def initCapacity := 8

/--
Get the root key and rest of terms of an expression using the specified config.
-/
private def rootKey (cfg: WhnfCoreConfig) (e : Expr) : MetaM (Key × Array Expr) :=
  pushArgs true (Array.mkEmpty initCapacity) e cfg

private partial def buildPath (op : Bool → Array Expr → Expr → MetaM (Key × Array Expr)) (root : Bool) (todo : Array Expr) (keys : Array Key) : MetaM (Array Key) := do
  if todo.isEmpty then
    return keys
  else
    let e    := todo.back!
    let todo := todo.pop
    let (k, todo) ← op root todo e
    buildPath op false todo (keys.push k)

/--
Create a key path from an expression using the function used for patterns.

This differs from Lean.Meta.DiscrTree.mkPath and targetPath in that the expression
should uses free variables rather than meta-variables for holes.
-/
def patternPath (e : Expr) (config : WhnfCoreConfig) : MetaM (Array Key) := do
  let todo : Array Expr := .mkEmpty initCapacity
  let op root todo e := pushArgs root todo e config
  buildPath op (root := true) (todo.push e) (.mkEmpty initCapacity)

/--
Create a key path from an expression we are matching against.

This should have mvars instantiated where feasible.
-/
def targetPath (e : Expr) (config : WhnfCoreConfig) : MetaM (Array Key) := do
  let todo : Array Expr := .mkEmpty initCapacity
  let op root todo e := do
        let (k, args) ← MatchClone.getMatchKeyArgs e root config
        pure (k, todo ++ args)
  buildPath op (root := true) (todo.push e) (.mkEmpty initCapacity)

/- Monad for finding matches while resolving deferred patterns. -/
@[reducible]
private def MatchM α := ReaderT WhnfCoreConfig (StateRefT (Array (Trie α)) MetaM)

private def runMatch (d : LazyDiscrTree α) (m : MatchM α β)  : MetaM (β × LazyDiscrTree α) := do
  let { config := c, tries := a, roots := r } := d
  let (result, a) ← withReducible $ (m.run c).run a
  pure (result, { config := c, tries := a, roots := r})

private def setTrie (i : TrieIndex) (v : Trie α) : MatchM α Unit :=
  modify (·.set! i v)

/-- Create a new trie with the given lazy entry. -/
private def newTrie [Monad m] [MonadState (Array (Trie α)) m] (e : LazyEntry α) : m TrieIndex := do
  modifyGet fun a => let sz := a.size; (sz, a.push (.node #[] 0 {} #[e]))

/-- Add a lazy entry to an existing trie. -/
private def addLazyEntryToTrie (i:TrieIndex) (e : LazyEntry α) : MatchM α Unit :=
  modify (·.modify i (·.pushPending e))

private def evalLazyEntry (config : WhnfCoreConfig)
    (p : Array α × TrieIndex × Std.HashMap Key TrieIndex)
    (entry : LazyEntry α)
    : MatchM α (Array α × TrieIndex × Std.HashMap Key TrieIndex) := do
  let (values, starIdx, children) := p
  let (todo, lctx, v) := entry
  if todo.isEmpty then
    let values := values.push v
    pure (values, starIdx, children)
  else
    let e    := todo.back!
    let todo := todo.pop
    let (k, todo) ← withLCtx lctx.1 lctx.2 $ pushArgs false todo e config
    if k == .star then
      if starIdx = 0 then
        let starIdx ← newTrie (todo, lctx, v)
        pure (values, starIdx, children)
      else
        addLazyEntryToTrie starIdx (todo, lctx, v)
        pure (values, starIdx, children)
    else
      match children[k]? with
      | none =>
        let children := children.insert k (← newTrie (todo, lctx, v))
        pure (values, starIdx, children)
      | some idx =>
        addLazyEntryToTrie idx (todo, lctx, v)
        pure (values, starIdx, children)

/--
This evaluates all lazy entries in a trie and updates `values`, `starIdx`, and `children`
accordingly.
-/
private partial def evalLazyEntries (config : WhnfCoreConfig)
    (values : Array α) (starIdx : TrieIndex) (children : Std.HashMap Key TrieIndex)
    (entries : Array (LazyEntry α)) :
    MatchM α (Array α × TrieIndex × Std.HashMap Key TrieIndex) := do
  let mut values := values
  let mut starIdx := starIdx
  let mut children := children
  entries.foldlM (init := (values, starIdx, children)) (evalLazyEntry config)

private def evalNode (c : TrieIndex) :
    MatchM α (Array α × TrieIndex × Std.HashMap Key TrieIndex) := do
  let .node vs star cs pending := (←get).get! c
  if pending.size = 0 then
    pure (vs, star, cs)
  else
    let config ← read
    setTrie c default
    let (vs, star, cs) ← evalLazyEntries config vs star cs pending
    setTrie c <| .node vs star cs #[]
    pure (vs, star, cs)

def dropKeyAux (next : TrieIndex) (rest : List Key) :
    MatchM α Unit :=
  if next = 0 then
    pure ()
  else do
    let (_, star, children) ← evalNode next
    match rest with
    | [] =>
      modify (·.set! next {values := #[], star, children})
    | k :: r => do
      let next := if k == .star then star else children.getD k 0
      dropKeyAux next r

/--
This drops a specific key from the lazy discrimination tree so that
all the entries matching that key exactly are removed.
-/
def dropKey (t : LazyDiscrTree α) (path : List LazyDiscrTree.Key) : MetaM (LazyDiscrTree α) :=
  match path with
  | [] => pure t
  | rootKey :: rest => do
    let idx := t.roots.getD rootKey 0
    Prod.snd <$> runMatch t (dropKeyAux idx rest)

/--
A match result contains the terms formed from matching a term against
patterns in the discrimination tree.

-/
structure MatchResult (α : Type) where
  /--
  The elements in the match result.

  The top-level array represents an array from `score` values to the
  results with that score. A `score` is the number of non-star matches
  in a pattern against the term, and thus bounded by the size of the
  term being matched against.  The elements of this array are themselves
  arrays of non-empty arrays so that we can defer concatenating results until
  needed.
  -/
  elts : Array (Array (Array α)) := #[]

namespace MatchResult

private def push (r : MatchResult α) (score : Nat) (e : Array α) : MatchResult α :=
  if e.isEmpty then
    r
  else if score < r.elts.size then
    { elts := r.elts.modify score (·.push e) }
  else
    let rec loop (a : Array (Array (Array α))) :=
        if a.size < score then
          loop (a.push #[])
        else
          { elts := a.push #[e] }
    termination_by score - a.size
    loop r.elts

/--
Number of elements in result
-/
partial def size (mr : MatchResult α) : Nat :=
  mr.elts.foldl (fun i a => a.foldl (fun n a => n + a.size) i) 0

/--
Append results to array
-/
@[specialize]
partial def appendResultsAux (mr : MatchResult α) (a : Array β) (f : Nat → α → β) : Array β :=
  let aa := mr.elts
  let n := aa.size
  Nat.fold (n := n) (init := a) fun i r =>
    let j := n-1-i
    let b := aa[j]!
    b.foldl (init := r) (· ++ ·.map (f j))

partial def appendResults (mr : MatchResult α) (a : Array α) : Array α :=
  mr.appendResultsAux a (fun _ a => a)

end MatchResult

/-
A partial match captures the intermediate state of a match
execution.

N.B. The discriminator tree in Lean has non-determinism due to
star and function arrows, so matching loop maintains a stack of
partial match results.
-/
structure PartialMatch where
  -- Remaining terms to match
  todo : Array Expr
  -- Number of non-star matches so far.
  score : Nat
  -- Trie to match next
  c : TrieIndex
  deriving Inhabited

/--
Evaluate all partial matches and add resulting matches to `MatchResult`.

The partial matches are stored in an array that is used as a stack. When adding
multiple partial matches to explore next, to ensure the order of results matches
user expectations, this code must add paths we want to prioritize and return
results earlier are added last.
-/
private partial def getMatchLoop (cases : Array PartialMatch) (result : MatchResult α) : MatchM α (MatchResult α) := do
  if cases.isEmpty then
    pure result
  else do
    let ca := cases.back!
    let cases := cases.pop
    let (vs, star, cs) ← evalNode ca.c
    if ca.todo.isEmpty then
      let result := result.push ca.score vs
      getMatchLoop cases result
    else if star == 0 && cs.isEmpty then
      getMatchLoop cases result
    else
      let e     := ca.todo.back!
      let todo  := ca.todo.pop
      /- We must always visit `Key.star` edges since they are wildcards.
          Thus, `todo` is not used linearly when there is `Key.star` edge
          and there is an edge for `k` and `k != Key.star`. -/
      let pushStar (cases : Array PartialMatch) :=
        if star = 0 then
          cases
        else
          cases.push { todo, score := ca.score, c := star }
      let pushNonStar (k : Key) (args : Array Expr) (cases : Array PartialMatch) :=
        match cs[k]? with
        | none   => cases
        | some c => cases.push { todo := todo ++ args, score := ca.score + 1, c }
      let cases := pushStar cases
      let (k, args) ← MatchClone.getMatchKeyArgs e (root := false) (← read)
      let cases :=
        match k with
        | .star  => cases
        /-
          Note: dep-arrow vs arrow
          Recall that dependent arrows are `(Key.other, #[])`, and non-dependent arrows are
          `(Key.arrow, #[a, b])`.
          A non-dependent arrow may be an instance of a dependent arrow (stored at `DiscrTree`).
          Thus, we also visit the `Key.other` child.
        -/
        | .arrow =>
          cases |> pushNonStar .other #[]
                |> pushNonStar k args
        | _      =>
          cases |> pushNonStar k args
      getMatchLoop cases result

private def getStarResult (root : Std.HashMap Key TrieIndex) : MatchM α (MatchResult α) :=
  match root[Key.star]? with
  | none =>
    pure <| {}
  | some idx => do
    let (vs, _) ← evalNode idx
    pure <| ({} : MatchResult α).push (score := 1) vs

/-
Add partial match to cases if discriminator tree root map has potential matches.
-/
private def pushRootCase (r : Std.HashMap Key TrieIndex) (k : Key) (args : Array Expr)
    (cases : Array PartialMatch) : Array PartialMatch :=
  match r[k]? with
  | none => cases
  | some c => cases.push { todo := args, score := 1, c }

/--
  Find values that match `e` in `root`.
-/
private def getMatchCore (root : Std.HashMap Key TrieIndex) (e : Expr) :
    MatchM α (MatchResult α) := do
  let result ← getStarResult root
  let (k, args) ← MatchClone.getMatchKeyArgs e (root := true) (← read)
  let cases :=
    match k with
    | .star  =>
      #[]
    /- See note about "dep-arrow vs arrow" at `getMatchLoop` -/
    | .arrow =>
      #[] |> pushRootCase root .other #[]
          |> pushRootCase root k args
    | _ =>
      #[] |> pushRootCase root k args
  getMatchLoop cases result

/--
  Find values that match `e` in `d`.

  The results are ordered so that the longest matches in terms of number of
  non-star keys are first with ties going to earlier operators first.
-/
def getMatch (d : LazyDiscrTree α) (e : Expr) : MetaM (MatchResult α × LazyDiscrTree α) :=
  withReducible <| runMatch d <| getMatchCore d.roots e

/--
Structure for quickly initializing a lazy discrimination tree with a large number
of elements using concurrent functions for generating entries.
-/
private structure PreDiscrTree (α : Type) where
  /-- Maps keys to index in tries array. -/
  roots : Std.HashMap Key Nat := {}
  /-- Lazy entries for root of trie. -/
  tries : Array (Array (LazyEntry α)) := #[]
  deriving Inhabited

namespace PreDiscrTree

private def modifyAt (d : PreDiscrTree α) (k : Key)
    (f : Array (LazyEntry α) → Array (LazyEntry α)) : PreDiscrTree α :=
  let { roots, tries } := d
  match roots[k]? with
  | .none =>
    let roots := roots.insert k tries.size
    { roots, tries := tries.push (f #[]) }
  | .some i =>
    { roots, tries := tries.modify i f }

/-- Add an entry to the pre-discrimination tree.-/
private def push (d : PreDiscrTree α) (k : Key) (e : LazyEntry α) : PreDiscrTree α :=
  d.modifyAt k (·.push e)

/-- Convert a pre-discrimination tree to a lazy discrimination tree. -/
private def toLazy (d : PreDiscrTree α) (config : WhnfCoreConfig := {}) : LazyDiscrTree α :=
  let { roots, tries } := d
  -- Adjust trie indices so the first value is reserved (so 0 is never a valid trie index)
  let roots := roots.fold (init := roots) (fun m k n => m.insert k (n+1))
  { config, roots, tries := #[default] ++ tries.map (.node {} 0 {}) }

/-- Merge two discrimination trees. -/
protected def append (x y : PreDiscrTree α) : PreDiscrTree α :=
  let (x, y, f) :=
        if x.roots.size ≥ y.roots.size then
          (x, y, fun y x => x ++ y)
        else
          (y, x, fun x y => x ++ y)
  let { roots := yk, tries := ya } := y
  yk.fold (init := x) fun d k yi => d.modifyAt k (f ya[yi]!)

instance : Append (PreDiscrTree α) where
  append := PreDiscrTree.append

end PreDiscrTree

/-- Initial entry in lazy discrimination tree -/
structure InitEntry (α : Type) where
  /-- Return root key for an entry. -/
  key : Key
  /-- Returns rest of entry for later insertion. -/
  entry : LazyEntry α

namespace InitEntry

/--
Constructs an initial entry from an expression and value.
-/
def fromExpr (expr : Expr) (value : α) (config : WhnfCoreConfig := {}) : MetaM (InitEntry α) := do
  let lctx ← getLCtx
  let linst ← getLocalInstances
  let lctx := (lctx, linst)
  let (key, todo) ← LazyDiscrTree.rootKey config expr
  pure <| { key, entry := (todo, lctx, value) }

/--
Creates an entry for a subterm of an initial entry.

This is slightly more efficient than using `fromExpr` on subterms since it avoids a redundant call
to `whnf`.
-/
def mkSubEntry (e : InitEntry α) (idx : Nat) (value : α) (config : WhnfCoreConfig := {}) :
    MetaM (InitEntry α) := do
  let (todo, lctx, _) := e.entry
  let (key, todo) ← LazyDiscrTree.rootKey config todo[idx]!
  pure <| { key, entry := (todo, lctx, value) }

end InitEntry

/-- Information about a failed import. -/
private structure ImportFailure where
  /-- Module with constant that import failed on. -/
  module  : Name
  /-- Constant that import failed on. -/
  const   : Name
  /-- Exception that triggers error. -/
  exception : Exception

/-- Information generation from imported modules. -/
private structure ImportData where
  errors : IO.Ref (Array ImportFailure)

private def ImportData.new : BaseIO ImportData := do
  let errors ← IO.mkRef #[]
  pure { errors }

structure Cache where
  ngen : NameGenerator
  core : Lean.Core.Cache
  meta : Lean.Meta.Cache

def Cache.empty (ngen : NameGenerator) : Cache := { ngen := ngen, core := {}, meta := {} }

def blacklistInsertion (env : Environment) (declName : Name) : Bool :=
  !allowCompletion env declName
  || declName == ``sorryAx
  || declName.isInternalDetail
  || (declName matches .str _ "inj")
  || (declName matches .str _ "noConfusionType")

private def addConstImportData
    (cctx : Core.Context)
    (env : Environment)
    (modName : Name)
    (d : ImportData)
    (cacheRef : IO.Ref Cache)
    (tree : PreDiscrTree α)
    (act : Name → ConstantInfo → MetaM (Array (InitEntry α)))
    (name : Name) (constInfo : ConstantInfo) : BaseIO (PreDiscrTree α) := do
  if constInfo.isUnsafe then return tree
  if blacklistInsertion env name then return tree
  let { ngen, core := core_cache, meta := meta_cache } ← cacheRef.get
  let mstate : Meta.State := { cache := meta_cache }
  cacheRef.set (Cache.empty ngen)
  let ctx : Meta.Context := { config := { transparency := .reducible } }
  let cm := (act name constInfo).run ctx mstate
  let cstate : Core.State := {env, cache := core_cache, ngen}
  match ←(cm.run cctx cstate).toBaseIO with
  | .ok ((a, ms), cs) =>
    cacheRef.set { ngen := cs.ngen, core := cs.cache, meta := ms.cache }
    pure <| a.foldl (fun t e => t.push e.key e.entry) tree
  | .error e =>
    let i : ImportFailure := {
      module := modName,
      const := name,
      exception := e
    }
    d.errors.modify (·.push i)
    pure tree

/--
Contains the pre discrimination tree and any errors occurring during initialization of
the library search tree.
-/
private structure InitResults (α : Type) where
  tree  : PreDiscrTree α := {}
  errors : Array ImportFailure := #[]

instance : Inhabited (InitResults α) where
  default := {}

namespace InitResults

/-- Combine two initial results. -/
protected def append (x y : InitResults α) : InitResults α :=
  let { tree := xv, errors := xe } := x
  let { tree := yv, errors := ye } := y
  { tree := xv ++ yv, errors := xe ++ ye }

instance : Append (InitResults α) where
  append := InitResults.append

end InitResults

private def toFlat (d : ImportData) (tree : PreDiscrTree α) :
    BaseIO (InitResults α) := do
  let de ← d.errors.swap #[]
  pure ⟨tree, de⟩

private partial def loadImportedModule
    (cctx : Core.Context)
    (env : Environment)
    (act : Name → ConstantInfo → MetaM (Array (InitEntry α)))
    (d : ImportData)
    (cacheRef : IO.Ref Cache)
    (tree : PreDiscrTree α)
    (mname : Name)
    (mdata : ModuleData)
    (i : Nat := 0) : BaseIO (PreDiscrTree α) := do
  if h : i < mdata.constNames.size then
    let name := mdata.constNames[i]
    let constInfo  := mdata.constants[i]!
    let tree ← addConstImportData cctx env mname d cacheRef tree act name constInfo
    loadImportedModule cctx env act d cacheRef tree mname mdata (i+1)
  else
    pure tree

private def createImportedEnvironmentSeq (cctx : Core.Context) (ngen : NameGenerator) (env : Environment)
    (act : Name → ConstantInfo → MetaM (Array (InitEntry α)))
    (start stop : Nat) : BaseIO (InitResults α) := do
      let cacheRef ← IO.mkRef (Cache.empty ngen)
      go (← ImportData.new) cacheRef {} start stop
    where go d cacheRef (tree : PreDiscrTree α) (start stop : Nat) : BaseIO _ := do
            if start < stop then
              let mname := env.header.moduleNames[start]!
              let mdata := env.header.moduleData[start]!
              let tree ← loadImportedModule cctx env act d cacheRef tree mname mdata
              go d cacheRef tree (start+1) stop
            else
              toFlat d tree
    termination_by stop - start

/-- Get the results of each task and merge using combining function -/
private def combineGet [Append α] (z : α) (tasks : Array (Task α)) : α :=
  tasks.foldl (fun x t => x ++ t.get) (init := z)

def getChildNgen [Monad M] [MonadNameGenerator M] : M NameGenerator := do
  let ngen ← getNGen
  let (cngen, ngen) := ngen.mkChild
  setNGen ngen
  pure cngen

def createLocalPreDiscrTree
    (cctx : Core.Context)
    (ngen : NameGenerator)
    (env : Environment)
    (d : ImportData)
    (act : Name → ConstantInfo → MetaM (Array (InitEntry α))) :
    BaseIO (PreDiscrTree α) := do
  let modName := env.header.mainModule
  let cacheRef ← IO.mkRef (Cache.empty ngen)
  let act (t : PreDiscrTree α) (n : Name) (c : ConstantInfo) : BaseIO (PreDiscrTree α) :=
        addConstImportData cctx env modName d cacheRef t act n c
  let r ← (env.constants.map₂.foldlM (init := {}) act : BaseIO (PreDiscrTree α))
  pure r

def dropKeys (t : LazyDiscrTree α) (keys : List (List LazyDiscrTree.Key)) : MetaM (LazyDiscrTree α) := do
  keys.foldlM (init := t) (·.dropKey ·)

def logImportFailure [Monad m] [MonadLog m] [AddMessageContext m] [MonadOptions m] (f : ImportFailure) : m Unit :=
  logError m!"Processing failure with {f.const} in {f.module}:\n  {f.exception.toMessageData}"

/-- Create a discriminator tree for imported environment. -/
def createImportedDiscrTree [Monad m] [MonadLog m] [AddMessageContext m] [MonadOptions m] [MonadLiftT BaseIO m]
    (cctx : Core.Context) (ngen : NameGenerator) (env : Environment)
    (act : Name → ConstantInfo → MetaM (Array (InitEntry α)))
    (constantsPerTask : Nat := 1000) :
    m (LazyDiscrTree α) := do
  let n := env.header.moduleData.size
  let rec
    /-- Allocate constants to tasks according to `constantsPerTask`. -/
    go ngen tasks start cnt idx := do
      if h : idx < env.header.moduleData.size then
        let mdata := env.header.moduleData[idx]
        let cnt := cnt + mdata.constants.size
        if cnt > constantsPerTask then
          let (childNGen, ngen) := ngen.mkChild
          let t ← liftM <| createImportedEnvironmentSeq cctx childNGen env act start (idx+1) |>.asTask
          go ngen (tasks.push t) (idx+1) 0 (idx+1)
        else
          go ngen tasks start cnt (idx+1)
      else
        if start < n then
          let (childNGen, _) := ngen.mkChild
          let t ← (createImportedEnvironmentSeq cctx childNGen env act start n).asTask
          pure (tasks.push t)
        else
          pure tasks
    termination_by env.header.moduleData.size - idx
  let tasks ← go ngen #[] 0 0 0
  let r := combineGet default tasks
  r.errors.forM logImportFailure
  pure <| r.tree.toLazy

/-- Creates the core context used for initializing a tree using the current context. -/
private def createTreeCtx (ctx : Core.Context) : Core.Context := {
    fileName := ctx.fileName
    fileMap := ctx.fileMap
    options := ctx.options
    maxRecDepth := ctx.maxRecDepth
    maxHeartbeats := 0
    ref := ctx.ref
    diag := getDiag ctx.options
  }

def findImportMatches
      (ext : EnvExtension (IO.Ref (Option (LazyDiscrTree α))))
      (addEntry : Name → ConstantInfo → MetaM (Array (InitEntry α)))
      (droppedKeys : List (List LazyDiscrTree.Key) := [])
      (constantsPerTask : Nat := 1000)
      (ty : Expr) : MetaM (MatchResult α) := do
  let cctx ← (read : CoreM Core.Context)
  let ngen ← getNGen
  let (cNGen, ngen) := ngen.mkChild
  setNGen ngen
  let dummy : IO.Ref (Option (LazyDiscrTree α)) ← IO.mkRef none
  let ref := @EnvExtension.getState _ ⟨dummy⟩ ext (←getEnv)
  let importTree ← (←ref.get).getDM $ do
    profileitM Exception  "lazy discriminator import initialization" (←getOptions) $ do
      let t ← createImportedDiscrTree (createTreeCtx cctx) cNGen (←getEnv) addEntry
                (constantsPerTask := constantsPerTask)
      dropKeys t droppedKeys
  let (importCandidates, importTree) ← importTree.getMatch ty
  ref.set (some importTree)
  pure importCandidates

/--
A discriminator tree for the current module's declarations only.

Note. We use different discriminator trees for imported and current module
declarations since imported declarations are typically much more numerous but
not changed after the environment is created.
-/
structure ModuleDiscrTreeRef (α : Type _)  where
  ref : IO.Ref (LazyDiscrTree α)

/-- Create a discriminator tree for current module declarations. -/
def createModuleDiscrTree
    (entriesForConst : Name → ConstantInfo → MetaM (Array (InitEntry α))) :
    CoreM (LazyDiscrTree α) := do
  let env ← getEnv
  let ngen ← getChildNgen
  let d ← ImportData.new
  let ctx ← read
  let t ← createLocalPreDiscrTree ctx ngen env d entriesForConst
  (← d.errors.get).forM logImportFailure
  pure <| t.toLazy

/--
Creates reference for lazy discriminator tree that only contains this module's definitions.
-/
def createModuleTreeRef (entriesForConst : Name → ConstantInfo → MetaM (Array (InitEntry α)))
    (droppedKeys : List (List LazyDiscrTree.Key)) : MetaM (ModuleDiscrTreeRef α) := do
  profileitM Exception "build module discriminator tree" (←getOptions) $ do
    let t ← createModuleDiscrTree entriesForConst
    let t ← dropKeys t droppedKeys
    pure { ref := ← IO.mkRef t }

/--
Returns candidates from this module in this module that match the expression.

* `moduleRef` is a references to a lazy discriminator tree only containing
this module's definitions.
-/
def findModuleMatches (moduleRef : ModuleDiscrTreeRef α) (ty : Expr) : MetaM (MatchResult α) := do
  profileitM Exception  "lazy discriminator local search" (← getOptions) $ do
    let discrTree ← moduleRef.ref.get
    let (localCandidates, localTree) ← discrTree.getMatch ty
    moduleRef.ref.set localTree
    pure localCandidates

/--
`findMatchesExt` searches for entries in a lazily initialized discriminator tree.

It provides some additional capabilities beyond `findMatches` to adjust results
based on priority and cache module declarations

* `modulesTreeRef` points to the discriminator tree for local environment.
  Used for caching and created by `createLocalTree`.
* `ext` should be an environment extension with an IO.Ref for caching the import lazy
   discriminator tree.
* `addEntry` is the function for creating discriminator tree entries from constants.
* `droppedKeys` contains keys we do not want to consider when searching for matches.
  It is used for dropping very general keys.
* `constantsPerTask` stores number of constants in imported modules used to
  decide when to create new task.
* `adjustResult` takes the priority and value to produce a final result.
* `ty` is the expression type.
-/
def findMatchesExt
    (moduleTreeRef : ModuleDiscrTreeRef α)
    (ext : EnvExtension (IO.Ref (Option (LazyDiscrTree α))))
    (addEntry : Name → ConstantInfo → MetaM (Array (InitEntry α)))
    (droppedKeys : List (List LazyDiscrTree.Key) := [])
    (constantsPerTask : Nat := 1000)
    (adjustResult : Nat → α → β)
    (ty : Expr) : MetaM (Array β) := do
  let moduleMatches ← findModuleMatches moduleTreeRef ty
  let importMatches ← findImportMatches ext addEntry droppedKeys constantsPerTask ty
  return Array.mkEmpty (moduleMatches.size + importMatches.size)
          |> moduleMatches.appendResultsAux (f := adjustResult)
          |> importMatches.appendResultsAux (f := adjustResult)

/--
`findMatches` searches for entries in a lazily initialized discriminator tree.

* `ext` should be an environment extension with an IO.Ref for caching the import lazy
   discriminator tree.
* `addEntry` is the function for creating discriminator tree entries from constants.
* `droppedKeys` contains keys we do not want to consider when searching for matches.
  It is used for dropping very general keys.
-/
def findMatches (ext : EnvExtension (IO.Ref (Option (LazyDiscrTree α))))
    (addEntry : Name → ConstantInfo → MetaM (Array (InitEntry α)))
    (droppedKeys : List (List LazyDiscrTree.Key) := [])
    (constantsPerTask : Nat := 1000)
    (ty : Expr) : MetaM (Array α) := do

  let moduleTreeRef ← createModuleTreeRef addEntry droppedKeys
  let incPrio _ v := v
  findMatchesExt moduleTreeRef ext addEntry droppedKeys constantsPerTask incPrio ty

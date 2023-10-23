/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.WHNF
import Lean.Meta.Transform
import Lean.Meta.DiscrTreeTypes

namespace Lean.Meta.DiscrTree
/-!
  (Imperfect) discrimination trees.
  We use a hybrid representation.
  - A `PersistentHashMap` for the root node which usually contains many children.
  - A sorted array of key/node pairs for inner nodes.

  The edges are labeled by keys:
  - Constant names (and arity). Universe levels are ignored.
  - Free variables (and arity). Thus, an entry in the discrimination tree
    may reference hypotheses from the local context.
  - Literals
  - Star/Wildcard. We use them to represent metavariables and terms
    we want to ignore. We ignore implicit arguments and proofs.
  - Other. We use to represent other kinds of terms (e.g., nested lambda, forall, sort, etc).

  We reduce terms using `TransparencyMode.reducible`. Thus, all reducible
  definitions in an expression `e` are unfolded before we insert it into the
  discrimination tree.

  Recall that projections from classes are **NOT** reducible.
  For example, the expressions `Add.add α (ringAdd ?α ?s) ?x ?x`
  and `Add.add Nat Nat.hasAdd a b` generates paths with the following keys
  respctively
  ```
  ⟨Add.add, 4⟩, *, *, *, *
  ⟨Add.add, 4⟩, *, *, ⟨a,0⟩, ⟨b,0⟩
  ```

  That is, we don't reduce `Add.add Nat inst a b` into `Nat.add a b`.
  We say the `Add.add` applications are the de-facto canonical forms in
  the metaprogramming framework.
  Moreover, it is the metaprogrammer's responsibility to re-pack applications such as
  `Nat.add a b` into `Add.add Nat inst a b`.

  Remark: we store the arity in the keys
  1- To be able to implement the "skip" operation when retrieving "candidate"
     unifiers.
  2- Distinguish partial applications `f a`, `f a b`, and `f a b c`.
-/

def Key.ctorIdx : Key → Nat
  | .star     => 0
  | .other    => 1
  | .lit ..   => 2
  | .fvar ..  => 3
  | .const .. => 4
  | .arrow    => 5
  | .proj ..  => 6

def Key.lt : Key → Key → Bool
  | .lit v₁,        .lit v₂        => v₁ < v₂
  | .fvar n₁ a₁,    .fvar n₂ a₂    => Name.quickLt n₁.name n₂.name || (n₁ == n₂ && a₁ < a₂)
  | .const n₁ a₁,   .const n₂ a₂   => Name.quickLt n₁ n₂ || (n₁ == n₂ && a₁ < a₂)
  | .proj s₁ i₁ a₁, .proj s₂ i₂ a₂ => Name.quickLt s₁ s₂ || (s₁ == s₂ && i₁ < i₂) || (s₁ == s₂ && i₁ == i₂ && a₁ < a₂)
  | k₁,             k₂             => k₁.ctorIdx < k₂.ctorIdx

instance : LT Key := ⟨fun a b => Key.lt a b⟩
instance (a b : Key) : Decidable (a < b) := inferInstanceAs (Decidable (Key.lt a b))

def Key.format : Key → Format
  | .star                   => "*"
  | .other                  => "◾"
  | .lit (Literal.natVal v) => Std.format v
  | .lit (Literal.strVal v) => repr v
  | .const k _              => Std.format k
  | .proj s i _             => Std.format s ++ "." ++ Std.format i
  | .fvar k _               => Std.format k.name
  | .arrow                  => "→"

instance : ToFormat Key := ⟨Key.format⟩

def Key.arity : Key → Nat
  | .const _ a  => a
  | .fvar _ a   => a
  | .arrow      => 2
  | .proj _ _ a => 1 + a
  | _           => 0

instance : Inhabited (Trie α) := ⟨.node #[] #[]⟩

def empty : DiscrTree α := { root := {} }

partial def Trie.format [ToFormat α] : Trie α → Format
  | .node vs cs => Format.group $ Format.paren $
    "node" ++ (if vs.isEmpty then Format.nil else " " ++ Std.format vs)
    ++ Format.join (cs.toList.map fun ⟨k, c⟩ => Format.line ++ Format.paren (Std.format k ++ " => " ++ format c))

instance [ToFormat α] : ToFormat (Trie α) := ⟨Trie.format⟩

partial def format [ToFormat α] (d : DiscrTree α) : Format :=
  let (_, r) := d.root.foldl
    (fun (p : Bool × Format) k c =>
      (false, p.2 ++ (if p.1 then Format.nil else Format.line) ++ Format.paren (Std.format k ++ " => " ++ Std.format c)))
    (true, Format.nil)
  Format.group r

instance [ToFormat α] : ToFormat (DiscrTree α) := ⟨format⟩

/-- The discrimination tree ignores implicit arguments and proofs.
   We use the following auxiliary id as a "mark". -/
private def tmpMVarId : MVarId := { name := `_discr_tree_tmp }
private def tmpStar := mkMVar tmpMVarId

instance : Inhabited (DiscrTree α) where
  default := {}

/--
  Return true iff the argument should be treated as a "wildcard" by the discrimination tree.

  - We ignore proofs because of proof irrelevance. It doesn't make sense to try to
    index their structure.

  - We ignore instance implicit arguments (e.g., `[Add α]`) because they are "morally" canonical.
    Moreover, we may have many definitionally equal terms floating around.
    Example: `Ring.hasAdd Int Int.isRing` and `Int.hasAdd`.

  - We considered ignoring implicit arguments (e.g., `{α : Type}`) since users don't "see" them,
    and may not even understand why some simplification rule is not firing.
    However, in type class resolution, we have instance such as `Decidable (@Eq Nat x y)`,
    where `Nat` is an implicit argument. Thus, we would add the path
    ```
    Decidable -> Eq -> * -> * -> * -> [Nat.decEq]
    ```
    to the discrimination tree IF we ignored the implicit `Nat` argument.
    This would be BAD since **ALL** decidable equality instances would be in the same path.
    So, we index implicit arguments if they are types.
    This setting seems sensible for simplification theorems such as:
    ```
    forall (x y : Unit), (@Eq Unit x y) = true
    ```
    If we ignore the implicit argument `Unit`, the `DiscrTree` will say it is a candidate
    simplification theorem for any equality in our goal.

  Remark: if users have problems with the solution above, we may provide a `noIndexing` annotation,
  and `ignoreArg` would return true for any term of the form `noIndexing t`.
-/
private def ignoreArg (a : Expr) (i : Nat) (infos : Array ParamInfo) : MetaM Bool := do
  if h : i < infos.size then
    let info := infos.get ⟨i, h⟩
    if info.isInstImplicit then
      return true
    else if info.isImplicit || info.isStrictImplicit then
      return not (← isType a)
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
  Return true if `e` is one of the following
  - A nat literal (numeral)
  - `Nat.zero`
  - `Nat.succ x` where `isNumeral x`
  - `OfNat.ofNat _ x _` where `isNumeral x` -/
private partial def isNumeral (e : Expr) : Bool :=
  if e.isNatLit then true
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
  Return true if `e` is one of the following
  - `Nat.add _ k` where `isNumeral k`
  - `Add.add Nat _ _ k` where `isNumeral k`
  - `HAdd.hAdd _ Nat _ _ k` where `isNumeral k`
  - `Nat.succ _`
  This function assumes `e.isAppOf fName`
-/
private def isOffset (fName : Name) (e : Expr) : MetaM Bool := do
  if fName == ``Nat.add && e.getAppNumArgs == 2 then
    return isNumeral e.appArg!
  else if fName == ``Add.add && e.getAppNumArgs == 4 then
    if (← isNatType (e.getArg! 0)) then return isNumeral e.appArg! else return false
  else if fName == ``HAdd.hAdd && e.getAppNumArgs == 6 then
    if (← isNatType (e.getArg! 1)) then return isNumeral e.appArg! else return false
  else
    return fName == ``Nat.succ && e.getAppNumArgs == 1

/--
  TODO: add hook for users adding their own functions for controlling `shouldAddAsStar`
  Different `DiscrTree` users may populate this set using, for example, attributes.

  Remark: we currently tag "offset" terms as star to avoid having to add special
  support for offset terms.
  Example, suppose the discrimination tree contains the entry
  `Nat.succ ?m |-> v`, and we are trying to retrieve the matches for `Expr.lit (Literal.natVal 1) _`.
  In this scenario, we want to retrieve `Nat.succ ?m |-> v`
-/
private def shouldAddAsStar (fName : Name) (e : Expr) : MetaM Bool := do
  isOffset fName e

def mkNoindexAnnotation (e : Expr) : Expr :=
  mkAnnotation `noindex e

def hasNoindexAnnotation (e : Expr) : Bool :=
  annotation? `noindex e |>.isSome

/--
Reduction procedure for the discrimination tree indexing.
The parameter `config` controls how aggressively the term is reduced.
The parameter at type `DiscrTree` controls this value.
See comment at `DiscrTree`.
-/
partial def reduce (e : Expr) (config : WhnfCoreConfig) : MetaM Expr := do
  let e ← whnfCore e config
  match (← unfoldDefinition? e) with
  | some e => reduce e config
  | none => match e.etaExpandedStrict? with
    | some e => reduce e config
    | none   => return e

/--
  Return `true` if `fn` is a "bad" key. That is, `pushArgs` would add `Key.other` or `Key.star`.
  We use this function when processing "root terms, and will avoid unfolding terms.
  Note that without this trick the pattern `List.map f ∘ List.map g` would be mapped into the key `Key.other`
  since the function composition `∘` would be unfolded and we would get `fun x => List.map g (List.map f x)`
-/
private def isBadKey (fn : Expr) : Bool :=
  match fn with
  | .lit ..   => false
  | .const .. => false
  | .fvar ..  => false
  | .proj ..  => false
  | .forallE _ _ b _ => b.hasLooseBVars
  | _ => true

/--
  Try to eliminate loose bound variables by performing beta-reduction.
  We use this method when processing terms in discrimination trees.
  These trees distinguish dependent arrows from nondependent ones.
  Recall that dependent arrows are indexed as `.other`, but nondependent arrows as `.arrow ..`.
  Motivation: we want to "discriminate" implications and simple arrows in our index.

  Now suppose we add the term `Foo (Nat → Nat)` to our index. The nested arrow appears as
  `.arrow ..`. Then, suppose we want to check whether the index contains
  `(x : Nat) → (fun _ => Nat) x`, but it will fail to retrieve `Foo (Nat → Nat)` because
  it assumes the nested arrow is a dependent one and uses `.other`.

  We use this method to address this issue by beta-reducing terms containing loose bound variables.
  See issue #2232.

  Remark: we expect the performance impact will be minimal.
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

/--
  Reduce `e` until we get an irreducible term (modulo current reducibility setting) or the resulting term
  is a bad key (see comment at `isBadKey`).
  We use this method instead of `reduce` for root terms at `pushArgs`. -/
private partial def reduceUntilBadKey (e : Expr) (config : WhnfCoreConfig) : MetaM Expr := do
  let e ← step e
  match e.etaExpandedStrict? with
  | some e => reduceUntilBadKey e config
  | none   => return e
where
  step (e : Expr) := do
    let e ← whnfCore e config
    match (← unfoldDefinition? e) with
    | some e' => if isBadKey e'.getAppFn then return e else step e'
    | none    => return e

/-- whnf for the discrimination tree module -/
def reduceDT (e : Expr) (root : Bool) (config : WhnfCoreConfig) : MetaM Expr :=
  if root then reduceUntilBadKey e config else reduce e config

/- Remark: we use `shouldAddAsStar` only for nested terms, and `root == false` for nested terms -/

private def pushArgs (root : Bool) (todo : Array Expr) (e : Expr) (config : WhnfCoreConfig) : MetaM (Key × Array Expr) := do
  if hasNoindexAnnotation e then
    return (.star, todo)
  else
    let e ← reduceDT e root config
    let fn := e.getAppFn
    let push (k : Key) (nargs : Nat) (todo : Array Expr): MetaM (Key × Array Expr) := do
      let info ← getFunInfoNArgs fn nargs
      let todo ← pushArgsAux info.paramInfo (nargs-1) e todo
      return (k, todo)
    match fn with
    | .lit v     =>
      return (.lit v, todo)
    | .const c _ =>
      unless root do
        if let some v := toNatLit? e then
          return (.lit v, todo)
        if (← shouldAddAsStar c e) then
          return (.star, todo)
      let nargs := e.getAppNumArgs
      push (.const c nargs) nargs todo
    | .proj s i a =>
      /-
      If `s` is a class, then `a` is an instance. Thus, we annotate `a` with `no_index` since we do not
      index instances. This should only happen if users mark a class projection function as `[reducible]`.

      TODO: add better support for projections that are functions
      -/
      let a := if isClass (← getEnv) s then mkNoindexAnnotation a else a
      let nargs := e.getAppNumArgs
      push (.proj s i nargs) nargs (todo.push a)
    | .fvar fvarId   =>
      let nargs := e.getAppNumArgs
      push (.fvar fvarId nargs) nargs todo
    | .mvar mvarId   =>
      if mvarId == tmpMVarId then
        -- We use `tmp to mark implicit arguments and proofs
        return (.star, todo)
      else if (← mvarId.isReadOnlyOrSyntheticOpaque) then
        return (.other, todo)
      else
        return (.star, todo)
    | .forallE _ d b _ =>
      -- See comment at elimLooseBVarsByBeta
      let b ← if b.hasLooseBVars then elimLooseBVarsByBeta b else pure b
      if b.hasLooseBVars then
        return (.other, todo)
      else
        return (.arrow, todo.push d |>.push b)
    | _ =>
      return (.other, todo)

partial def mkPathAux (root : Bool) (todo : Array Expr) (keys : Array Key) (config : WhnfCoreConfig) : MetaM (Array Key) := do
  if todo.isEmpty then
    return keys
  else
    let e    := todo.back
    let todo := todo.pop
    let (k, todo) ← pushArgs root todo e config
    mkPathAux false todo (keys.push k) config

private def initCapacity := 8

def mkPath (e : Expr) (config : WhnfCoreConfig) : MetaM (Array Key) := do
  withReducible do
    let todo : Array Expr := .mkEmpty initCapacity
    let keys : Array Key := .mkEmpty initCapacity
    mkPathAux (root := true) (todo.push e) keys config

private partial def createNodes (keys : Array Key) (v : α) (i : Nat) : Trie α :=
  if h : i < keys.size then
    let k := keys.get ⟨i, h⟩
    let c := createNodes keys v (i+1)
    .node #[] #[(k, c)]
  else
    .node #[v] #[]

/--
If `vs` contains an element `v'` such that `v == v'`, then replace `v'` with `v`.
Otherwise, push `v`.
See issue #2155
Recall that `BEq α` may not be Lawful.
-/
private def insertVal [BEq α] (vs : Array α) (v : α) : Array α :=
  loop 0
where
  loop (i : Nat) : Array α :=
    if h : i < vs.size then
      if v == vs[i] then
        vs.set ⟨i,h⟩ v
      else
        loop (i+1)
    else
      vs.push v
termination_by loop i => vs.size - i

private partial def insertAux [BEq α] (keys : Array Key) (v : α) (config : WhnfCoreConfig) : Nat → Trie α → Trie α
  | i, .node vs cs =>
    if h : i < keys.size then
      let k := keys.get ⟨i, h⟩
      let c := Id.run $ cs.binInsertM
          (fun a b => a.1 < b.1)
          (fun ⟨_, s⟩ => let c := insertAux keys v config (i+1) s; (k, c)) -- merge with existing
          (fun _ => let c := createNodes keys v (i+1); (k, c))
          (k, default)
      .node vs c
    else
      .node (insertVal vs v) cs

def insertCore [BEq α] (d : DiscrTree α) (keys : Array Key) (v : α) (config : WhnfCoreConfig) : DiscrTree α :=
  if keys.isEmpty then panic! "invalid key sequence"
  else
    let k := keys[0]!
    match d.root.find? k with
    | none =>
      let c := createNodes keys v 1
      { root := d.root.insert k c }
    | some c =>
      let c := insertAux keys v config 1 c
      { root := d.root.insert k c }

def insert [BEq α] (d : DiscrTree α) (e : Expr) (v : α) (config : WhnfCoreConfig) : MetaM (DiscrTree α) := do
  let keys ← mkPath e config
  return d.insertCore keys v config

private def getKeyArgs (e : Expr) (isMatch root : Bool) (config : WhnfCoreConfig) : MetaM (Key × Array Expr) := do
  let e ← reduceDT e root config
  unless root do
    -- See pushArgs
    if let some v := toNatLit? e then
      return (.lit v, #[])
  match e.getAppFn with
  | .lit v         => return (.lit v, #[])
  | .const c _     =>
    if (← getConfig).isDefEqStuckEx && e.hasExprMVar then
      if (← isReducible c) then
        /- `e` is a term `c ...` s.t. `c` is reducible and `e` has metavariables, but it was not unfolded.
           This can happen if the metavariables in `e` are "blocking" smart unfolding.
           If `isDefEqStuckEx` is enabled, then we must throw the `isDefEqStuck` exception to postpone TC resolution.
           Here is an example. Suppose we have
           ```
            inductive Ty where
              | bool | fn (a ty : Ty)


            @[reducible] def Ty.interp : Ty → Type
              | bool   => Bool
              | fn a b => a.interp → b.interp
           ```
           and we are trying to synthesize `BEq (Ty.interp ?m)`
        -/
        Meta.throwIsDefEqStuck
      else if let some matcherInfo := isMatcherAppCore? (← getEnv) e then
        -- A matcher application is stuck is one of the discriminants has a metavariable
        let args := e.getAppArgs
        for arg in args[matcherInfo.getFirstDiscrPos: matcherInfo.getFirstDiscrPos + matcherInfo.numDiscrs] do
          if arg.hasExprMVar then
            Meta.throwIsDefEqStuck
      else if (← isRec c) then
        /- Similar to the previous case, but for `match` and recursor applications. It may be stuck (i.e., did not reduce)
           because of metavariables. -/
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
  | _ =>
    return (.other, #[])

private abbrev getMatchKeyArgs (e : Expr) (root : Bool) (config : WhnfCoreConfig) : MetaM (Key × Array Expr) :=
  getKeyArgs e (isMatch := true) (root := root) (config := config)

private abbrev getUnifyKeyArgs (e : Expr) (root : Bool) (config : WhnfCoreConfig) : MetaM (Key × Array Expr) :=
  getKeyArgs e (isMatch := false) (root := root) (config := config)

private def getStarResult (d : DiscrTree α) : Array α :=
  let result : Array α := .mkEmpty initCapacity
  match d.root.find? .star with
  | none                  => result
  | some (.node vs _) => result ++ vs

private abbrev findKey (cs : Array (Key × Trie α)) (k : Key) : Option (Key × Trie α) :=
  cs.binSearch (k, default) (fun a b => a.1 < b.1)

private partial def getMatchLoop (todo : Array Expr) (c : Trie α) (result : Array α) (config : WhnfCoreConfig) : MetaM (Array α) := do
  match c with
  | .node vs cs =>
    if todo.isEmpty then
      return result ++ vs
    else if cs.isEmpty then
      return result
    else
      let e     := todo.back
      let todo  := todo.pop
      let first := cs[0]! /- Recall that `Key.star` is the minimal key -/
      let (k, args) ← getMatchKeyArgs e (root := false) config
      /- We must always visit `Key.star` edges since they are wildcards.
         Thus, `todo` is not used linearly when there is `Key.star` edge
         and there is an edge for `k` and `k != Key.star`. -/
      let visitStar (result : Array α) : MetaM (Array α) :=
        if first.1 == .star then
          getMatchLoop todo first.2 result config
        else
          return result
      let visitNonStar (k : Key) (args : Array Expr) (result : Array α) : MetaM (Array α) :=
        match findKey cs k with
        | none   => return result
        | some c => getMatchLoop (todo ++ args) c.2 result config
      let result ← visitStar result
      match k with
      | .star  => return result
      /-
        Note: dep-arrow vs arrow
        Recall that dependent arrows are `(Key.other, #[])`, and non-dependent arrows are `(Key.arrow, #[a, b])`.
        A non-dependent arrow may be an instance of a dependent arrow (stored at `DiscrTree`). Thus, we also visit the `Key.other` child.
      -/
      | .arrow => visitNonStar .other #[] (← visitNonStar k args result)
      | _      => visitNonStar k args result

private def getMatchRoot (d : DiscrTree α) (k : Key) (args : Array Expr) (result : Array α) (config : WhnfCoreConfig) : MetaM (Array α) :=
  match d.root.find? k with
  | none   => return result
  | some c => getMatchLoop args c result config

private def getMatchCore (d : DiscrTree α) (e : Expr) (config : WhnfCoreConfig) : MetaM (Key × Array α) :=
  withReducible do
    let result := getStarResult d
    let (k, args) ← getMatchKeyArgs e (root := true) config
    match k with
    | .star  => return (k, result)
    /- See note about "dep-arrow vs arrow" at `getMatchLoop` -/
    | .arrow => return (k, (← getMatchRoot d k args (← getMatchRoot d .other #[] result config) config))
    | _      => return (k, (← getMatchRoot d k args result config))

/--
  Find values that match `e` in `d`.
-/
def getMatch (d : DiscrTree α) (e : Expr) (config : WhnfCoreConfig) : MetaM (Array α) :=
  return (← getMatchCore d e config).2

/--
  Similar to `getMatch`, but returns solutions that are prefixes of `e`.
  We store the number of ignored arguments in the result.-/
partial def getMatchWithExtra (d : DiscrTree α) (e : Expr) (config : WhnfCoreConfig) : MetaM (Array (α × Nat)) := do
  let (k, result) ← getMatchCore d e config
  let result := result.map (·, 0)
  if !e.isApp then
    return result
  else if !(← mayMatchPrefix k) then
    return result
  else
    go e.appFn! 1 result
where
  mayMatchPrefix (k : Key) : MetaM Bool :=
    let cont (k : Key) : MetaM Bool :=
      if d.root.find? k |>.isSome then
        return true
      else
        mayMatchPrefix k
    match k with
    | .const f (n+1)  => cont (.const f n)
    | .fvar f (n+1)   => cont (.fvar f n)
    | .proj s i (n+1) => cont (.proj s i n)
    | _               => return false

  go (e : Expr) (numExtra : Nat) (result : Array (α × Nat)) : MetaM (Array (α × Nat)) := do
    let result := result ++ (← getMatchCore d e config).2.map (., numExtra)
    if e.isApp then
      go e.appFn! (numExtra + 1) result
    else
      return result

partial def getUnify (d : DiscrTree α) (e : Expr) (config : WhnfCoreConfig) : MetaM (Array α) :=
  withReducible do
    let (k, args) ← getUnifyKeyArgs e (root := true) config
    match k with
    | .star => d.root.foldlM (init := #[]) fun result k c => process k.arity #[] c result
    | _ =>
      let result := getStarResult d
      match d.root.find? k with
      | none   => return result
      | some c => process 0 args c result
where
  process (skip : Nat) (todo : Array Expr) (c : Trie α) (result : Array α) : MetaM (Array α) := do
    match skip, c with
    | skip+1, .node _  cs =>
      if cs.isEmpty then
        return result
      else
        cs.foldlM (init := result) fun result ⟨k, c⟩ => process (skip + k.arity) todo c result
    | 0, .node vs cs => do
      if todo.isEmpty then
        return result ++ vs
      else if cs.isEmpty then
        return result
      else
        let e     := todo.back
        let todo  := todo.pop
        let (k, args) ← getUnifyKeyArgs e (root := false) config
        let visitStar (result : Array α) : MetaM (Array α) :=
          let first := cs[0]!
          if first.1 == .star then
            process 0 todo first.2 result
          else
            return result
        let visitNonStar (k : Key) (args : Array Expr) (result : Array α) : MetaM (Array α) :=
          match findKey cs k with
          | none   => return result
          | some c => process 0 (todo ++ args) c.2 result
        match k with
        | .star  => cs.foldlM (init := result) fun result ⟨k, c⟩ => process k.arity todo c result
        -- See comment a `getMatch` regarding non-dependent arrows vs dependent arrows
        | .arrow => visitNonStar .other #[] (← visitNonStar k args (← visitStar result))
        | _      => visitNonStar k args (← visitStar result)

end Lean.Meta.DiscrTree

/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jannis Limperg, Kim Morrison
-/
prelude
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
  respectively
  ```
  ⟨Add.add, 4⟩, α, *, *, *
  ⟨Add.add, 4⟩, Nat, *, ⟨a,0⟩, ⟨b,0⟩
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
  | .star            => "*"
  | .other           => "◾"
  | .lit (.natVal v) => Std.format v
  | .lit (.strVal v) => repr v
  | .const k _       => Std.format k
  | .proj s i _      => Std.format s ++ "." ++ Std.format i
  | .fvar k _        => Std.format k.name
  | .arrow           => "∀"

instance : ToFormat Key := ⟨Key.format⟩

/--
Helper function for converting an entry (i.e., `Array Key`) to the discrimination tree into
`MessageData` that is more user-friendly. We use this function to implement diagnostic information.
-/
partial def keysAsPattern (keys : Array Key) : CoreM MessageData := do
  go (parenIfNonAtomic := false) |>.run' keys.toList
where
  next? : StateRefT (List Key) CoreM (Option Key) := do
    let key :: keys ← get | return none
    set keys
    return some key

  mkApp (f : MessageData) (args : Array MessageData) (parenIfNonAtomic : Bool) : CoreM MessageData := do
    if args.isEmpty then
      return f
    else
      let mut r := f
      for arg in args do
        r := r ++ m!" {arg}"
      if parenIfNonAtomic then
        return m!"({r})"
      else
        return r

  go (parenIfNonAtomic := true) : StateRefT (List Key) CoreM MessageData := do
    let some key ← next? | return .nil
    match key with
    | .const declName nargs =>
      mkApp m!"{← mkConstWithLevelParams declName}" (← goN nargs) parenIfNonAtomic
    | .fvar fvarId nargs =>
      mkApp m!"{mkFVar fvarId}" (← goN nargs) parenIfNonAtomic
    | .proj _ i nargs =>
      mkApp m!"{← go}.{i+1}" (← goN nargs) parenIfNonAtomic
    | .arrow =>
      mkApp m!"∀ " (← goN 1) parenIfNonAtomic
    | .star => return "_"
    | .other => return "<other>"
    | .lit (.natVal v) => return m!"{v}"
    | .lit (.strVal v) => return m!"{v}"

  goN (num : Nat) : StateRefT (List Key) CoreM (Array MessageData) := do
    let mut r := #[]
    for _ in [: num] do
      r := r.push (← go)
    return r

def Key.arity : Key → Nat
  | .const _ a  => a
  | .fvar _ a   => a
  /-
  Remark: `.arrow` used to have arity 2, and was used to encode only **non**-dependent
  arrows. However, this feature was a recurrent source of bugs. For example, a
  theorem about a dependent arrow can be applied to a non-dependent one. The
  reverse direction may also happen. See issue #2835. Therefore, `.arrow` was made
  to have arity 0. But this throws away easy to use information, and makes it so
  that ∀ and ∃ behave quite differently. So now `.arrow` at least indexes the
  domain of the forall (whether dependent or non-dependent).
  -/
  | .arrow      => 1
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
  Return true if `e` is one of the following
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
  | .lit ..     => false
  | .const ..   => false
  | .fvar ..    => false
  | .proj ..    => false
  | .forallE .. => false
  | _           => true

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

/--
Append `n` wildcards to `todo`
-/
private def pushWildcards (n : Nat) (todo : Array Expr) : Array Expr :=
  match n with
  | 0   => todo
  | n+1 => pushWildcards n (todo.push tmpStar)

/--
When `noIndexAtArgs := true`, `pushArgs` assumes function application arguments have a `no_index` annotation.
That is, `f a b` is indexed as it was `f (no_index a) (no_index b)`.
This feature is used when indexing local proofs in the simplifier. This is useful in examples like the one described on issue #2670.
In this issue, we have a local hypotheses `(h : ∀ p : α × β, f p p.2 = p.2)`, and users expect it to be applicable to
`f (a, b) b = b`. This worked in Lean 3 since no indexing was used. We can retrieve Lean 3 behavior by writing
`(h : ∀ p : α × β, f p (no_index p.2) = p.2)`, but this is very inconvenient when the hypotheses was not written by the user in first place.
For example, it was introduced by another tactic. Thus, when populating the discrimination tree explicit arguments provided to `simp` (e.g., `simp [h]`),
we use `noIndexAtArgs := true`. See comment: https://github.com/leanprover/lean4/issues/2670#issuecomment-1758889365
-/
private def pushArgs (root : Bool) (todo : Array Expr) (e : Expr) (config : WhnfCoreConfig) (noIndexAtArgs : Bool) : MetaM (Key × Array Expr) := do
  if hasNoindexAnnotation e then
    return (.star, todo)
  else
    let e ← reduceDT e root config
    let fn := e.getAppFn
    let push (k : Key) (nargs : Nat) (todo : Array Expr): MetaM (Key × Array Expr) := do
      let info ← getFunInfoNArgs fn nargs
      let todo ← if noIndexAtArgs then
        pure <| pushWildcards nargs todo
      else
        pushArgsAux info.paramInfo (nargs-1) e todo
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
    | .forallE _n d _ _ =>
      return (.arrow, todo.push d)
    | _ => return (.other, todo)

@[inherit_doc pushArgs]
partial def mkPathAux (root : Bool) (todo : Array Expr) (keys : Array Key) (config : WhnfCoreConfig) (noIndexAtArgs : Bool) : MetaM (Array Key) := do
  if todo.isEmpty then
    return keys
  else
    let e    := todo.back!
    let todo := todo.pop
    let (k, todo) ← pushArgs root todo e config noIndexAtArgs
    mkPathAux false todo (keys.push k) config noIndexAtArgs

private def initCapacity := 8

@[inherit_doc pushArgs]
def mkPath (e : Expr) (config : WhnfCoreConfig) (noIndexAtArgs := false) : MetaM (Array Key) := do
  withReducible do
    let todo : Array Expr := .mkEmpty initCapacity
    let keys : Array Key := .mkEmpty initCapacity
    mkPathAux (root := true) (todo.push e) keys config noIndexAtArgs

private partial def createNodes (keys : Array Key) (v : α) (i : Nat) : Trie α :=
  if h : i < keys.size then
    let k := keys[i]
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
        vs.set i v
      else
        loop (i+1)
    else
      vs.push v
  termination_by vs.size - i

private partial def insertAux [BEq α] (keys : Array Key) (v : α) : Nat → Trie α → Trie α
  | i, .node vs cs =>
    if h : i < keys.size then
      let k := keys[i]
      let c := Id.run $ cs.binInsertM
          (fun a b => a.1 < b.1)
          (fun ⟨_, s⟩ => let c := insertAux keys v (i+1) s; (k, c)) -- merge with existing
          (fun _ => let c := createNodes keys v (i+1); (k, c))
          (k, default)
      .node vs c
    else
      .node (insertVal vs v) cs

def insertCore [BEq α] (d : DiscrTree α) (keys : Array Key) (v : α) : DiscrTree α :=
  if keys.isEmpty then panic! "invalid key sequence"
  else
    let k := keys[0]!
    match d.root.find? k with
    | none =>
      let c := createNodes keys v 1
      { root := d.root.insert k c }
    | some c =>
      let c := insertAux keys v 1 c
      { root := d.root.insert k c }

def insert [BEq α] (d : DiscrTree α) (e : Expr) (v : α) (config : WhnfCoreConfig) (noIndexAtArgs := false) : MetaM (DiscrTree α) := do
  let keys ← mkPath e config noIndexAtArgs
  return d.insertCore keys v

/--
Inserts a value into a discrimination tree,
but only if its key is not of the form `#[*]` or `#[=, *, *, *]`.
-/
def insertIfSpecific [BEq α] (d : DiscrTree α) (e : Expr) (v : α) (config : WhnfCoreConfig) (noIndexAtArgs := false) : MetaM (DiscrTree α) := do
  let keys ← mkPath e config noIndexAtArgs
  return if keys == #[Key.star] || keys == #[Key.const `Eq 3, Key.star, Key.star, Key.star] then
    d
  else
    d.insertCore keys v

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
  | .forallE _ d _ _ => return (.arrow, #[d])
  | _ => return (.other, #[])

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
      let e     := todo.back!
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

/--
Return the root symbol for `e`, and the number of arguments after `reduceDT`.
-/
def getMatchKeyRootFor (e : Expr) (config : WhnfCoreConfig) : MetaM (Key × Nat) := do
  let e ← reduceDT e (root := true) config
  let numArgs := e.getAppNumArgs
  let key := match e.getAppFn with
    | .lit v         => .lit v
    | .fvar fvarId   => .fvar fvarId numArgs
    | .mvar _        => .other
    | .proj s i _ .. => .proj s i numArgs
    | .forallE ..    => .arrow
    | .const c _     =>
      -- This method is used by the simplifier only, we do **not** support
      -- (← getConfig).isDefEqStuckEx
      .const c numArgs
    | _ => .other
  return (key, numArgs)

/--
Get all results under key `k`.
-/
private partial def getAllValuesForKey (d : DiscrTree α) (k : Key) (result : Array α) : Array α :=
  match d.root.find? k with
  | none      => result
  | some trie => go trie result
where
  go (trie : Trie α) (result : Array α) : Array α := Id.run do
    match trie with
    | .node vs cs =>
      let mut result := result ++ vs
      for (_, trie) in cs do
        result := go trie result
      return result

/--
A liberal version of `getMatch` which only takes the root symbol of `e` into account.
We use this method to simulate Lean 3's indexing.

The natural number in the result is the number of arguments in `e` after `reduceDT`.
-/
def getMatchLiberal (d : DiscrTree α) (e : Expr) (config : WhnfCoreConfig) : MetaM (Array α × Nat) := do
  withReducible do
    let result := getStarResult d
    let (k, numArgs) ← getMatchKeyRootFor e config
    match k with
    | .star  => return (result, numArgs)
    | _      => return (getAllValuesForKey d k result, numArgs)

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
        let e     := todo.back!
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
        | _      => visitNonStar k args (← visitStar result)

namespace Trie

/--
Monadically fold the keys and values stored in a `Trie`.
-/
partial def foldM [Monad m] (initialKeys : Array Key)
    (f : σ → Array Key → α → m σ) : (init : σ) → Trie α → m σ
  | init, Trie.node vs children => do
    let s ← vs.foldlM (init := init) fun s v => f s initialKeys v
    children.foldlM (init := s) fun s (k, t) =>
      t.foldM (initialKeys.push k) f s

/--
Fold the keys and values stored in a `Trie`.
-/
@[inline]
def fold (initialKeys : Array Key) (f : σ → Array Key → α → σ) (init : σ) (t : Trie α) : σ :=
  Id.run <| t.foldM initialKeys (init := init) fun s k a => return f s k a

/--
Monadically fold the values stored in a `Trie`.
-/
partial def foldValuesM [Monad m] (f : σ → α → m σ) : (init : σ) → Trie α → m σ
  | init, node vs children => do
    let s ← vs.foldlM (init := init) f
    children.foldlM (init := s) fun s (_, c) => c.foldValuesM (init := s) f

/--
Fold the values stored in a `Trie`.
-/
@[inline]
def foldValues (f : σ → α → σ) (init : σ) (t : Trie α) : σ :=
  Id.run <| t.foldValuesM (init := init) f

/--
The number of values stored in a `Trie`.
-/
partial def size : Trie α → Nat
  | Trie.node vs children =>
    children.foldl (init := vs.size) fun n (_, c) => n + size c

end Trie


/--
Monadically fold over the keys and values stored in a `DiscrTree`.
-/
@[inline]
def foldM [Monad m] (f : σ → Array Key → α → m σ) (init : σ)
    (t : DiscrTree α) : m σ :=
  t.root.foldlM (init := init) fun s k t => t.foldM #[k] (init := s) f

/--
Fold over the keys and values stored in a `DiscrTree`
-/
@[inline]
def fold (f : σ → Array Key → α → σ) (init : σ) (t : DiscrTree α) : σ :=
  Id.run <| t.foldM (init := init) fun s keys a => return f s keys a

/--
Monadically fold over the values stored in a `DiscrTree`.
-/
@[inline]
def foldValuesM [Monad m] (f : σ → α → m σ) (init : σ) (t : DiscrTree α) :
    m σ :=
  t.root.foldlM (init := init) fun s _ t => t.foldValuesM (init := s) f

/--
Fold over the values stored in a `DiscrTree`.
-/
@[inline]
def foldValues (f : σ → α → σ) (init : σ) (t : DiscrTree α) : σ :=
  Id.run <| t.foldValuesM (init := init) f

/--
Check for the presence of a value satisfying a predicate.
-/
@[inline]
def containsValueP (t : DiscrTree α) (f : α → Bool) : Bool :=
  t.foldValues (init := false) fun r a => r || f a

/--
Extract the values stored in a `DiscrTree`.
-/
@[inline]
def values (t : DiscrTree α) : Array α :=
  t.foldValues (init := #[]) fun as a => as.push a

/--
Extract the keys and values stored in a `DiscrTree`.
-/
@[inline]
def toArray (t : DiscrTree α) : Array (Array Key × α) :=
  t.fold (init := #[]) fun as keys a => as.push (keys, a)

/--
Get the number of values stored in a `DiscrTree`. O(n) in the size of the tree.
-/
@[inline]
def size (t : DiscrTree α) : Nat :=
  t.root.foldl (init := 0) fun n _ t => n + t.size

variable {m : Type → Type} [Monad m]

/-- Apply a monadic function to the array of values at each node in a `DiscrTree`. -/
partial def Trie.mapArraysM (t : DiscrTree.Trie α) (f : Array α → m (Array β)) :
    m (DiscrTree.Trie β) :=
  match t with
  | .node vs children =>
    return .node (← f vs) (← children.mapM fun (k, t') => do pure (k, ← t'.mapArraysM f))

/-- Apply a monadic function to the array of values at each node in a `DiscrTree`. -/
def mapArraysM (d : DiscrTree α) (f : Array α → m (Array β)) : m (DiscrTree β) := do
  pure { root := ← d.root.mapM (fun t => t.mapArraysM f) }

/-- Apply a function to the array of values at each node in a `DiscrTree`. -/
def mapArrays (d : DiscrTree α) (f : Array α → Array β) : DiscrTree β :=
  Id.run <| d.mapArraysM fun A => pure (f A)

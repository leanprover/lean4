/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.Basic
import Lean.Meta.FunInfo
import Lean.Meta.InferType
import Lean.Meta.WHNF

namespace Lean.Meta.DiscrTree
/-
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
  | Key.star     => 0
  | Key.other    => 1
  | Key.lit ..   => 2
  | Key.fvar ..  => 3
  | Key.const .. => 4
  | Key.arrow    => 5
  | Key.proj ..  => 6

def Key.lt : Key → Key → Bool
  | Key.lit v₁,      Key.lit v₂      => v₁ < v₂
  | Key.fvar n₁ a₁,  Key.fvar n₂ a₂  => Name.quickLt n₁.name n₂.name || (n₁ == n₂ && a₁ < a₂)
  | Key.const n₁ a₁, Key.const n₂ a₂ => Name.quickLt n₁ n₂ || (n₁ == n₂ && a₁ < a₂)
  | Key.proj s₁ i₁,  Key.proj s₂ i₂  => Name.quickLt s₁ s₂ || (s₁ == s₂ && i₁ < i₂)
  | k₁,              k₂              => k₁.ctorIdx < k₂.ctorIdx

instance : LT Key := ⟨fun a b => Key.lt a b⟩
instance (a b : Key) : Decidable (a < b) := inferInstanceAs (Decidable (Key.lt a b))

def Key.format : Key → Format
  | Key.star                   => "*"
  | Key.other                  => "◾"
  | Key.lit (Literal.natVal v) => Std.format v
  | Key.lit (Literal.strVal v) => repr v
  | Key.const k _              => Std.format k
  | Key.proj s i               => Std.format s ++ "." ++ Std.format i
  | Key.fvar k _               => Std.format k.name
  | Key.arrow                  => "→"

instance : ToFormat Key := ⟨Key.format⟩

def Key.arity : Key → Nat
  | Key.const _ a => a
  | Key.fvar _ a  => a
  | Key.arrow     => 2
  | Key.proj ..   => 1
  | _             => 0

instance : Inhabited (Trie α) := ⟨Trie.node #[] #[]⟩

def empty : DiscrTree α := { root := {} }

partial def Trie.format [ToFormat α] : Trie α → Format
  | Trie.node vs cs => Format.group $ Format.paren $
    "node" ++ (if vs.isEmpty then Format.nil else " " ++ Std.format vs)
    ++ Format.join (cs.toList.map $ fun ⟨k, c⟩ => Format.line ++ Format.paren (Std.format k ++ " => " ++ format c))

instance [ToFormat α] : ToFormat (Trie α) := ⟨Trie.format⟩

partial def format [ToFormat α] (d : DiscrTree α) : Format :=
  let (_, r) := d.root.foldl
    (fun (p : Bool × Format) k c =>
      (false, p.2 ++ (if p.1 then Format.nil else Format.line) ++ Format.paren (Std.format k ++ " => " ++ Std.format c)))
    (true, Format.nil)
  Format.group r

instance [ToFormat α] : ToFormat (DiscrTree α) := ⟨format⟩

/- The discrimination tree ignores implicit arguments and proofs.
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
    to the discrimination tree IF we ignored the implict `Nat` argument.
    This would be BAD since **ALL** decidable equality instances would be in the same path.
    So, we index implicit arguments if they are types.
    This setting seems sensible for simplification lemmas such as:
    ```
    forall (x y : Unit), (@Eq Unit x y) = true
    ```
    If we ignore the implicit argument `Unit`, the `DiscrTree` will say it is a candidate
    simplification lemma for any equality in our goal.

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
  | i, Expr.app f a _, todo => do
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

/-
  TODO: add hook for users adding their own functions for controlling `shouldAddAsStar`
  Different `DiscrTree` users may populate this set using, for example, attributes.

  Remark: we currently tag `Nat.zero` and "offset" terms to avoid having to add special
  support for `Expr.lit` and offset terms.
  Example, suppose the discrimination tree contains the entry
  `Nat.succ ?m |-> v`, and we are trying to retrieve the matches for `Expr.lit (Literal.natVal 1) _`.
  In this scenario, we want to retrieve `Nat.succ ?m |-> v` -/
private def shouldAddAsStar (fName : Name) (e : Expr) : MetaM Bool := do
  if fName == `Nat.zero then
    return true
  else
    isOffset fName e

def mkNoindexAnnotation (e : Expr) : Expr :=
  mkAnnotation `noindex e

def hasNoindexAnnotation (e : Expr) : Bool :=
  annotation? `noindex e |>.isSome

private partial def whnfEta (e : Expr) : MetaM Expr := do
  let e ← whnf e
  match e.etaExpandedStrict? with
  | some e => whnfEta e
  | none   => return e

/--
  Return `true` if `fn` is a "bad" key. That is, `pushArgs` would add `Key.other` or `Key.star`.
  We use this function when processing "root terms, and will avoid unfolding terms.
  Note that without this trick the pattern `List.map f ∘ List.map g` would be mapped into the key `Key.other`
  since the function composition `∘` would be unfolded and we would get `fun x => List.map g (List.map f x)`
-/
private def isBadKey (fn : Expr) : Bool :=
  match fn with
  | Expr.lit ..   => false
  | Expr.const .. => false
  | Expr.fvar ..  => false
  | Expr.proj ..  => false
  | Expr.forallE _ d b _ => b.hasLooseBVars
  | _ => true

/--
  Reduce `e` until we get an irreducible term (modulo current reducibility setting) or the resulting term
  is a bad key (see comment at `isBadKey`).
  We use this method instead of `whnfEta` for root terms at `pushArgs`. -/
private partial def whnfUntilBadKey (e : Expr) : MetaM Expr := do
  let e ← step e
  match e.etaExpandedStrict? with
  | some e => whnfUntilBadKey e
  | none   => return e
where
  step (e : Expr) := do
    let e ← whnfCore e
    match (← unfoldDefinition? e) with
    | some e' => if isBadKey e' then return e else step e'
    | none    => return e

/-- whnf for the discrimination tree module -/
private def whnfDT (e : Expr) (root : Bool) : MetaM Expr :=
  if root then whnfUntilBadKey e else whnfEta e

/- Remark: we use `shouldAddAsStar` only for nested terms, and `root == false` for nested terms -/

private def pushArgs (root : Bool) (todo : Array Expr) (e : Expr) : MetaM (Key × Array Expr) := do
  if hasNoindexAnnotation e then
    return (Key.star, todo)
  else
    let e ← whnfDT e root
    let fn := e.getAppFn
    let push (k : Key) (nargs : Nat) : MetaM (Key × Array Expr) := do
      let info ← getFunInfoNArgs fn nargs
      let todo ← pushArgsAux info.paramInfo (nargs-1) e todo
      return (k, todo)
    match fn with
    | Expr.lit v _       => return (Key.lit v, todo)
    | Expr.const c _ _   =>
      unless root do
        if (← shouldAddAsStar c e) then
          return (Key.star, todo)
      let nargs := e.getAppNumArgs
      push (Key.const c nargs) nargs
    | Expr.proj s i a .. =>
      return (Key.proj s i, todo.push a)
    | Expr.fvar fvarId _ =>
      let nargs := e.getAppNumArgs
      push (Key.fvar fvarId nargs) nargs
    | Expr.mvar mvarId _ =>
      if mvarId == tmpMVarId then
        -- We use `tmp to mark implicit arguments and proofs
        return (Key.star, todo)
      else if (← isReadOnlyOrSyntheticOpaqueExprMVar mvarId) then
        return (Key.other, todo)
      else
        return (Key.star, todo)
    | Expr.forallE _ d b _ =>
      if b.hasLooseBVars then
        return (Key.other, todo)
      else
        return (Key.arrow, todo.push d |>.push b)
    | _ =>
      return (Key.other, todo)

partial def mkPathAux (root : Bool) (todo : Array Expr) (keys : Array Key) : MetaM (Array Key) := do
  if todo.isEmpty then
    return keys
  else
    let e    := todo.back
    let todo := todo.pop
    let (k, todo) ← pushArgs root todo e
    mkPathAux false todo (keys.push k)

private def initCapacity := 8

def mkPath (e : Expr) : MetaM (Array Key) := do
  withReducible do
    let todo : Array Expr := Array.mkEmpty initCapacity
    let keys : Array Key  := Array.mkEmpty initCapacity
    mkPathAux (root := true) (todo.push e) keys

private partial def createNodes (keys : Array Key) (v : α) (i : Nat) : Trie α :=
  if h : i < keys.size then
    let k := keys.get ⟨i, h⟩
    let c := createNodes keys v (i+1)
    Trie.node #[] #[(k, c)]
  else
    Trie.node #[v] #[]

private def insertVal [BEq α] (vs : Array α) (v : α) : Array α :=
  if vs.contains v then vs else vs.push v

private partial def insertAux [BEq α] (keys : Array Key) (v : α) : Nat → Trie α → Trie α
  | i, Trie.node vs cs =>
    if h : i < keys.size then
      let k := keys.get ⟨i, h⟩
      let c := Id.run $ cs.binInsertM
          (fun a b => a.1 < b.1)
          (fun ⟨_, s⟩ => let c := insertAux keys v (i+1) s; (k, c)) -- merge with existing
          (fun _ => let c := createNodes keys v (i+1); (k, c))
          (k, arbitrary)
      Trie.node vs c
    else
      Trie.node (insertVal vs v) cs

def insertCore [BEq α] (d : DiscrTree α) (keys : Array Key) (v : α) : DiscrTree α :=
  if keys.isEmpty then panic! "invalid key sequence"
  else
    let k := keys[0]
    match d.root.find? k with
    | none =>
      let c := createNodes keys v 1
      { root := d.root.insert k c }
    | some c =>
      let c := insertAux keys v 1 c
      { root := d.root.insert k c }

def insert [BEq α] (d : DiscrTree α) (e : Expr) (v : α) : MetaM (DiscrTree α) := do
  let keys ← mkPath e
  return d.insertCore keys v

private def getKeyArgs (e : Expr) (isMatch root : Bool) : MetaM (Key × Array Expr) := do
  let e ← whnfDT e root
  match e.getAppFn with
  | Expr.lit v _       => return (Key.lit v, #[])
  | Expr.const c _ _   =>
    let nargs := e.getAppNumArgs
    return (Key.const c nargs, e.getAppRevArgs)
  | Expr.fvar fvarId _ =>
    let nargs := e.getAppNumArgs
    return (Key.fvar fvarId nargs, e.getAppRevArgs)
  | Expr.mvar mvarId _ =>
    if isMatch then
      return (Key.other, #[])
    else do
      let ctx ← read
      if ctx.config.isDefEqStuckEx then
        /-
          When the configuration flag `isDefEqStuckEx` is set to true,
          we want `isDefEq` to throw an exception whenever it tries to assign
          a read-only metavariable.
          This feature is useful for type class resolution where
          we may want to notify the caller that the TC problem may be solveable
          later after it assigns `?m`.
          The method `DiscrTree.getUnify e` returns candidates `c` that may "unify" with `e`.
          That is, `isDefEq c e` may return true. Now, consider `DiscrTree.getUnify d (Add ?m)`
          where `?m` is a read-only metavariable, and the discrimination tree contains the keys
          `HadAdd Nat` and `Add Int`. If `isDefEqStuckEx` is set to true, we must treat `?m` as
          a regular metavariable here, otherwise we return the empty set of candidates.
          This is incorrect because it is equivalent to saying that there is no solution even if
          the caller assigns `?m` and try again. -/
        return (Key.star, #[])
      else if (← isReadOnlyOrSyntheticOpaqueExprMVar mvarId) then
        return (Key.other, #[])
      else
        return (Key.star, #[])
  | Expr.proj s i a .. =>
    return (Key.proj s i, #[a])
  | Expr.forallE _ d b _ =>
    if b.hasLooseBVars then
      return (Key.other, #[])
    else
      return (Key.arrow, #[d, b])
  | _ =>
    return (Key.other, #[])

private abbrev getMatchKeyArgs (e : Expr) (root : Bool) : MetaM (Key × Array Expr) :=
  getKeyArgs e (isMatch := true) (root := root)

private abbrev getUnifyKeyArgs (e : Expr) (root : Bool) : MetaM (Key × Array Expr) :=
  getKeyArgs e (isMatch := false) (root := root)

private def getStarResult (d : DiscrTree α) : Array α :=
  let result : Array α := Array.mkEmpty initCapacity
  match d.root.find? Key.star with
  | none                  => result
  | some (Trie.node vs _) => result ++ vs

private abbrev findKey (cs : Array (Key × Trie α)) (k : Key) : Option (Key × Trie α) :=
  cs.binSearch (k, arbitrary) (fun a b => a.1 < b.1)

private partial def getMatchLoop (todo : Array Expr) (c : Trie α) (result : Array α) : MetaM (Array α) := do
  match c with
  | Trie.node vs cs =>
    if todo.isEmpty then
      return result ++ vs
    else if cs.isEmpty then
      return result
    else
      let e     := todo.back
      let todo  := todo.pop
      let first := cs[0] /- Recall that `Key.star` is the minimal key -/
      let (k, args) ← getMatchKeyArgs e (root := false)
      /- We must always visit `Key.star` edges since they are wildcards.
         Thus, `todo` is not used linearly when there is `Key.star` edge
         and there is an edge for `k` and `k != Key.star`. -/
      let visitStar (result : Array α) : MetaM (Array α) :=
        if first.1 == Key.star then
          getMatchLoop todo first.2 result
        else
          return result
      let visitNonStar (k : Key) (args : Array Expr) (result : Array α) : MetaM (Array α) :=
        match findKey cs k with
        | none   => result
        | some c => getMatchLoop (todo ++ args) c.2 result
      let result ← visitStar result
      match k with
      | Key.star  => result
      /-
        Recall that dependent arrows are `(Key.other, #[])`, and non-dependent arrows are `(Key.arrow, #[a, b])`.
        A non-dependent arrow may be an instance of a dependent arrow (stored at `DiscrTree`). Thus, we also visit the `Key.other` child.
      -/
      | Key.arrow => visitNonStar Key.other #[] (← visitNonStar k args result)
      | _         => visitNonStar k args result

private def getMatchRoot (d : DiscrTree α) (k : Key) (args : Array Expr) (result : Array α) : MetaM (Array α) :=
  match d.root.find? k with
  | none   => return result
  | some c => getMatchLoop args c result

/--
  Find values that match `e` in `d`.
-/
partial def getMatch (d : DiscrTree α) (e : Expr) : MetaM (Array α) :=
  withReducible do
    let result := getStarResult d
    let (k, args) ← getMatchKeyArgs e (root := true)
    match k with
    | Key.star => return result
    | _        => getMatchRoot d k args result

/--
  Similar to `getMatch`, but returns solutions that are prefixes of `e`.
  We store the number of ignored arguments in the result.-/
partial def getMatchWithExtra (d : DiscrTree α) (e : Expr) : MetaM (Array (α × Nat)) :=
  withReducible do
    let result := getStarResult d |>.map (., 0)
    let (k, args) ← getMatchKeyArgs e (root := true)
    match k with
    | Key.star => return result
    | _        => process k args 0 result
where
  process (k : Key) (args : Array Expr) (numExtraArgs : Nat) (result : Array (α × Nat)) : MetaM (Array (α × Nat)) := do
    let result := result ++ ((← getMatchRoot d k args #[]).map (., numExtraArgs))
    match k with
    | Key.const f 0     => return result
    | Key.const f (n+1) => process (Key.const f n) args.pop (numExtraArgs + 1) result
    | Key.fvar f 0      => return result
    | Key.fvar f (n+1)  => process (Key.fvar f n) args.pop (numExtraArgs + 1) result
    | _                 => return result

partial def getUnify (d : DiscrTree α) (e : Expr) : MetaM (Array α) :=
  withReducible do
    let (k, args) ← getUnifyKeyArgs e (root := true)
    match k with
    | Key.star => d.root.foldlM (init := #[]) fun result k c => process k.arity #[] c result
    | _ =>
      let result := getStarResult d
      match d.root.find? k with
      | none   => return result
      | some c => process 0 args c result
where
  process (skip : Nat) (todo : Array Expr) (c : Trie α) (result : Array α) : MetaM (Array α) := do
    match skip, c with
    | skip+1, Trie.node vs cs =>
      if cs.isEmpty then
        return result
      else
        cs.foldlM (init := result) fun result ⟨k, c⟩ => process (skip + k.arity) todo c result
    | 0, Trie.node vs cs => do
      if todo.isEmpty then
        return result ++ vs
      else if cs.isEmpty then
        return result
      else
        let e     := todo.back
        let todo  := todo.pop
        let (k, args) ← getUnifyKeyArgs e (root := false)
        let visitStar (result : Array α) : MetaM (Array α) :=
          let first := cs[0]
          if first.1 == Key.star then
            process 0 todo first.2 result
          else
            return result
        let visitNonStar (k : Key) (args : Array Expr) (result : Array α) : MetaM (Array α) :=
          match findKey cs k with
          | none   => result
          | some c => process 0 (todo ++ args) c.2 result
        match k with
        | Key.star  => cs.foldlM (init := result) fun result ⟨k, c⟩ => process k.arity todo c result
        -- See comment a `getMatch` regarding non-dependent arrows vs dependent arrows
        | Key.arrow => visitNonStar Key.other #[] (← visitNonStar k args (← visitStar result))
        | _         => visitNonStar k args (← visitStar result)

end Lean.Meta.DiscrTree

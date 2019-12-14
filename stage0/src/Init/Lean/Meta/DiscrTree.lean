/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Lean.Meta.Basic
import Init.Lean.Meta.FunInfo
import Init.Lean.Meta.InferType

namespace Lean
namespace Meta
namespace DiscrTree

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
  For example, the expressions `HasAdd.add α (ringHasAdd ?α ?s) ?x ?x`
  and `HasAdd.add Nat Nat.hasAdd a b` generates paths with the following keys
  respctively
  ```
  ⟨HasAdd.add, 4⟩, *, *, *, *
  ⟨HasAdd.add, 4⟩, *, *, ⟨a,0⟩, ⟨b,0⟩
  ```
  That is, we don't reduce `HasAdd.add Nat Nat.HasAdd a b` into `Nat.add a b`.
  We say the `HasAdd.add` applications are the de-facto canonical forms in
  the metaprogramming framework.
  Moreover, it is the metaprammer resposability to re-pack applications such as
  `Nat.add a b` into `HasAdd.add Nat Nat.hasAdd a b`.

  Remark: we store the arity in the keys
  1- To be able to implement the "skip" operation when retrieving "candidate"
     unifiers.
  2- Distinguish partial applications `f a`, `f a b`, and `f a b c`.
-/

def Key.ctorIdx : Key → Nat
| Key.star      => 0
| Key.other     => 1
| Key.lit _     => 2
| Key.fvar _ _  => 3
| Key.const _ _ => 4

def Key.lt : Key → Key → Bool
| Key.lit v₁,      Key.lit v₂      => v₁ < v₂
| Key.fvar n₁ a₁,  Key.fvar n₂ a₂  => Name.quickLt n₁ n₂ || (n₁ == n₂ && a₁ < a₂)
| Key.const n₁ a₁, Key.const n₂ a₂ => Name.quickLt n₁ n₂ || (n₁ == n₂ && a₁ < a₂)
| k₁,              k₂              => k₁.ctorIdx < k₂.ctorIdx

instance Key.hasLess : HasLess Key := ⟨fun a b => Key.lt a b⟩

def Key.format : Key → Format
| Key.star                   => "*"
| Key.other                  => "◾"
| Key.lit (Literal.natVal v) => fmt v
| Key.lit (Literal.strVal v) => repr v
| Key.const k _              => fmt k
| Key.fvar k _               => fmt k

instance Key.hasFormat : HasFormat Key := ⟨Key.format⟩

def Key.arity : Key → Nat
| Key.const _ a => a
| Key.fvar _ a  => a
| _             => 0

instance Trie.inhabited {α} : Inhabited (Trie α) := ⟨Trie.node #[] #[]⟩

def empty {α} : DiscrTree α := { root := {} }

/- The discrimination tree ignores implicit arguments and proofs.
   We use the following auxiliary id as a "mark". -/
private def tmpMVarId : MVarId := `_discr_tree_tmp
private def tmpStar := mkMVar tmpMVarId

instance {α} : Inhabited (DiscrTree α) := ⟨{}⟩

/--
  Return true iff the argument should be treated as a "wildcard" by the discrimination tree.

  - We ignore proofs because of proof irrelevance. It doesn't make sense to try to
    index their structure.

  - We ignore instance implicit arguments (e.g., `[HasAdd α]`) because they are "morally" canonical.
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
private def ignoreArg (a : Expr) (i : Nat) (infos : Array ParamInfo) : MetaM Bool :=
if h : i < infos.size then
  let info := infos.get ⟨i, h⟩;
  if info.instImplicit then
    pure true
  else if info.implicit then
    not <$> isType a
  else
    isProof a
else
  isProof a

private partial def pushArgsAux (infos : Array ParamInfo) : Nat → Expr → Array Expr → MetaM (Array Expr)
| i, Expr.app f a _, todo =>
  condM (ignoreArg a i infos)
    (pushArgsAux (i-1) f (todo.push tmpStar))
    (pushArgsAux (i-1) f (todo.push a))
| _, _, todo => pure todo

private partial def whnfEta : Expr → MetaM Expr
| e => do
  e ← whnf e;
  match e.etaExpandedStrict? with
  | some e => whnfEta e
  | none   => pure e

private def pushArgs (todo : Array Expr) (e : Expr) : MetaM (Key × Array Expr) := do
e ← whnfEta e;
let fn := e.getAppFn;
let push (k : Key) (nargs : Nat) : MetaM (Key × Array Expr) := do {
  info ← getFunInfoNArgs fn nargs;
  todo ← pushArgsAux info.paramInfo (nargs-1) e todo;
  pure (k, todo)
};
match fn with
| Expr.lit v _       => pure (Key.lit v, todo)
| Expr.const c _ _   => let nargs := e.getAppNumArgs; push (Key.const c nargs) nargs
| Expr.fvar fvarId _ => let nargs := e.getAppNumArgs; push (Key.fvar fvarId nargs) nargs
| Expr.mvar mvarId _ =>
  if mvarId == tmpMVarId then
    -- We use `tmp to mark implicit arguments and proofs
    pure (Key.star, todo)
  else condM (isReadOnlyOrSyntheticExprMVar mvarId)
    (pure (Key.other, todo))
    (pure (Key.star, todo))
| _                  => pure (Key.other, todo)

partial def mkPathAux : Array Expr → Array Key → MetaM (Array Key)
| todo, keys =>
  if todo.isEmpty then
    pure keys
  else do
    let e    := todo.back;
    let todo := todo.pop;
    (k, todo) ← pushArgs todo e;
    mkPathAux todo (keys.push k)

private def initCapacity := 8

def mkPath (e : Expr) : MetaM (Array Key) :=
withTransparency TransparencyMode.reducible $ do
  let todo : Array Expr := Array.mkEmpty initCapacity;
  let keys : Array Key  := Array.mkEmpty initCapacity;
  mkPathAux (todo.push e) keys

private partial def createNodes {α} (keys : Array Key) (v : α) : Nat → Trie α
| i =>
  if h : i < keys.size then
    let k := keys.get ⟨i, h⟩;
    let c := createNodes (i+1);
    Trie.node #[] #[(k, c)]
  else
    Trie.node #[v] #[]

private def insertVal {α} [HasBeq α] (vs : Array α) (v : α) : Array α :=
if vs.contains v then vs else vs.push v

private partial def insertAux {α} [HasBeq α] (keys : Array Key) (v : α) : Nat → Trie α → Trie α
| i, Trie.node vs cs =>
  if h : i < keys.size then
    let k := keys.get ⟨i, h⟩;
    let c := Id.run $ cs.binInsertM
        (fun a b => a.1 < b.1)
        (fun ⟨_, s⟩ => let c := insertAux (i+1) s; (k, c)) -- merge with existing
        (fun _ => let c := createNodes keys v (i+1); (k, c))
        (k, arbitrary _);
    Trie.node vs c
  else
    Trie.node (insertVal vs v) cs

def insertCore {α} [HasBeq α] (d : DiscrTree α) (keys : Array Key) (v : α) : DiscrTree α :=
if keys.isEmpty then panic! "invalid key sequence"
else
  let k := keys.get! 0;
  match d.root.find k with
  | none =>
    let c := createNodes keys v 1;
    { root := d.root.insert k c }
  | some c =>
    let c := insertAux keys v 1 c;
    { root := d.root.insert k c }

def insert {α} [HasBeq α] (d : DiscrTree α) (e : Expr) (v : α) : MetaM (DiscrTree α) := do
keys ← mkPath e;
pure $ d.insertCore keys v

partial def Trie.format {α} [HasFormat α] : Trie α → Format
| Trie.node vs cs => Format.group $ Format.paren $
  "node" ++ (if vs.isEmpty then Format.nil else " " ++ fmt vs)
  ++ Format.join (cs.toList.map $ fun ⟨k, c⟩ => Format.line ++ Format.paren (fmt k ++ " => " ++ Trie.format c))

instance Trie.hasFormat {α} [HasFormat α] : HasFormat (Trie α) := ⟨Trie.format⟩

partial def format {α} [HasFormat α] (d : DiscrTree α) : Format :=
let (_, r) := d.root.foldl
  (fun (p : Bool × Format) k c =>
    (false, p.2 ++ (if p.1 then Format.nil else Format.line) ++ Format.paren (fmt k ++ " => " ++ fmt c)))
  (true, Format.nil);
Format.group r

instance DiscrTree.hasFormat {α} [HasFormat α] : HasFormat (DiscrTree α) := ⟨format⟩

private def getKeyArgs (e : Expr) (isMatch? : Bool) : MetaM (Key × Array Expr) := do
e ← whnfEta e;
match e.getAppFn with
| Expr.lit v _       => pure (Key.lit v, #[])
| Expr.const c _ _   => let nargs := e.getAppNumArgs; pure (Key.const c nargs, e.getAppRevArgs)
| Expr.fvar fvarId _ => let nargs := e.getAppNumArgs; pure (Key.fvar fvarId nargs, e.getAppRevArgs)
| Expr.mvar mvarId _ =>
  if isMatch? then pure (Key.other, #[])
  else do
    ctx ← read;
    if ctx.config.isDefEqStuckEx then
      /-
        When the configuration flag `isDefEqStuckEx` is set to true,
        we want `isDefEq` to throw an exception whenever it tries to assign
        a read-only metavariable.
        This feature is useful for type class resolution where
        we may want to notify the caller that the TC problem may be solveable
        later after it assigns `?m`.
        The method `DiscrTree.getUnify e` returns candidates `c` that may "unify" with `e`.
        That is, `isDefEq c e` may return true. Now, consider `DiscrTree.getUnify d (HasAdd ?m)`
        where `?m` is a read-only metavariable, and the discrimination tree contains the keys
        `HadAdd Nat` and `HasAdd Int`. If `isDefEqStuckEx` is set to true, we must treat `?m` as
        a regular metavariable here, otherwise we return the empty set of candidates.
        This is incorrect because it is equivalent to saying that there is no solution even if
        the caller assigns `?m` and try again. -/
      pure (Key.star, #[])
    else
      condM (isReadOnlyOrSyntheticExprMVar mvarId)
        (pure (Key.other, #[]))
        (pure (Key.star, #[]))
| _                  => pure (Key.other, #[])

private abbrev getMatchKeyArgs (e : Expr) : MetaM (Key × Array Expr) :=
getKeyArgs e true

private abbrev getUnifyKeyArgs (e : Expr) : MetaM (Key × Array Expr) :=
getKeyArgs e false

private partial def getMatchAux {α} : Array Expr → Trie α → Array α → MetaM (Array α)
| todo, Trie.node vs cs, result =>
  if todo.isEmpty then pure $ result ++ vs
  else if cs.isEmpty then pure result
  else do
    let e     := todo.back;
    let todo  := todo.pop;
    let first := cs.get! 0; /- Recall that `Key.star` is the minimal key -/
    (k, args) ← getMatchKeyArgs e;
    /- We must always visit `Key.star` edges since they are wildcards.
       Thus, `todo` is not used linearly when there is `Key.star` edge
       and there is an edge for `k` and `k != Key.star`. -/
    let visitStarChild (result : Array α) : MetaM (Array α) := if first.1 == Key.star then getMatchAux todo first.2 result else pure result;
    match k with
    | Key.star => visitStarChild result
    | _ =>
      match cs.binSearch (k, arbitrary _) (fun a b => a.1 < b.1) with
      | none   => visitStarChild result
      | some c => do result ← visitStarChild result; getMatchAux (todo ++ args) c.2 result

private def getStarResult {α} (d : DiscrTree α) : Array α :=
let result : Array α := Array.mkEmpty initCapacity;
match d.root.find Key.star with
| none                  => result
| some (Trie.node vs _) => result ++ vs

def getMatch {α} (d : DiscrTree α) (e : Expr) : MetaM (Array α) :=
withTransparency TransparencyMode.reducible $ do
  let result := getStarResult d;
  (k, args) ← getMatchKeyArgs e;
  match k with
  | Key.star => pure result
  | _        =>
    match d.root.find k with
    | none   => pure result
    | some c => getMatchAux args c result

private partial def getUnifyAux {α} : Nat → Array Expr → Trie α → (Array α) → MetaM (Array α)
| skip+1, todo, Trie.node vs cs, result =>
  if cs.isEmpty then pure result
  else cs.foldlM (fun result ⟨k, c⟩ => getUnifyAux (skip + k.arity) todo c result) result
| 0, todo, Trie.node vs cs, result =>
  if todo.isEmpty then pure (result ++ vs)
  else if cs.isEmpty then pure result
  else do
    let e     := todo.back;
    let todo  := todo.pop;
    (k, args) ← getUnifyKeyArgs e;
    match k with
    | Key.star => cs.foldlM (fun result ⟨k, c⟩ => getUnifyAux k.arity todo c result) result
    | _ =>
      let first := cs.get! 0;
      let visitStarChild (result : Array α) : MetaM (Array α) :=
        if first.1 == Key.star then getUnifyAux 0 todo first.2 result else pure result;
      match cs.binSearch (k, arbitrary _) (fun a b => a.1 < b.1) with
      | none   => visitStarChild result
      | some c => do result ← visitStarChild result; getUnifyAux 0 (todo ++ args) c.2 result

def getUnify {α} (d : DiscrTree α) (e : Expr) : MetaM (Array α) :=
withTransparency TransparencyMode.reducible $ do
  (k, args) ← getUnifyKeyArgs e;
  match k with
  | Key.star => d.root.foldlM (fun result k c => getUnifyAux k.arity #[] c result) #[]
  | _ =>
    let result := getStarResult d;
    match d.root.find k with
    | none   => pure result
    | some c => getUnifyAux 0 args c result

end DiscrTree
end Meta
end Lean

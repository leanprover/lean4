/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/
module

prelude

public import Lean.Kernel.InLean.ExprEq
public import Lean.Util.InstantiateLevelParams
import all Init.Util

/-!
# InLean: the expression operations, in Lean

Core's opaque C++ operations — `instantiate`, `instantiate1`, `instantiateRev(Range)`,
`abstract(Range)`, `lift`/`lowerLooseBVars`, `hasLooseBVar`, and the
`implemented_by` traversals (`Expr.replace`, `Expr.find?`,
`collectFVars`, `getUsedConstants`, the level-parameter collector) — are
replaced by Lean-defined, memoised structural walks: twins of
`ConLeche.Cached.ExprOpsC`'s substitutions (`instantiate1C`,
`instantiateListC`, `instantiateRev`, `abstract1C`, `abstractRangeC`,
`instLevelParams`) over `Lean.Expr`'s six binder-bearing constructors.

**The memo** is con-leche's: a walk memoises exactly the nodes the runtime
reports shared (`withExclusive`, `Lean.Kernel.InLean.Exclusive`), keyed by address and
binder offset, every entry carrying its own proof against the plain
descent (`mapP`, `anyP`) — a structural recursion, no fuel needed.

**The cutoffs** read Lean's cached fields (`looseBVarRange`, `hasFVar`,
`hasLevelParam`), as con-leche's read its computed `data` word.  Lean
computes them in C (`Expr.mkData`, `Expr.mkAppData`, `Level.mkData`); the
proof relates them to the term by what C computes, on terms in range.  Lean does not
saturate the range: a node above `2^20 - 1` loose variables aborts the
process ("too many bound variables").  So the one walk here that can grow
indices past a term's own, `abstract`, writes `rangePoison` instead of an
out-of-range `bvar`, and its checker call sites error on it in O(1)
(`abstractRangeM`, `Lean.Kernel.InLean.StateC`).
-/

@[expose] public section

namespace Lean.Kernel.InLean

open Lean

/-! ## Level equality (twin of `Level.beq`/`beqPtr`) -/

def Level.beqI (a b : Level) : Bool := decide (a = b)

@[inline] def Level.beqPtrI (a b : Level) : Bool :=
  withPtrEq a b (fun _ => decide (a = b)) (fun h => by subst h; simp)

@[csimp] theorem Level.beqI_eq_beqPtrI : @Level.beqI = @Level.beqPtrI := by
  funext a b; rfl

scoped instance instBEqLevelI : BEq Level := ⟨Level.beqI⟩

scoped instance : LawfulBEq Level where
  eq_of_beq h := of_decide_eq_true h
  rfl := by simp [BEq.beq, Level.beqI]

namespace Lvl

/-- Twin of `Level.subst.go`. -/
def substGo : List Name → List Level → Name → Level
  | k :: ks, v :: vs, n => if k == n then v else substGo ks vs n
  | _, _, n => .param n

/-- Twin of `Level.subst` (no simplification, unlike Lean's
`Level.instantiateParams`). -/
def subst (ks : List Name) (vs : List Level) : Level → Level
  | .zero => .zero
  | .succ l => .succ (subst ks vs l)
  | .max l r => .max (subst ks vs l) (subst ks vs r)
  | .imax l r => .imax (subst ks vs l) (subst ks vs r)
  | .param n => substGo ks vs n
  | .mvar m => .mvar m

/-- A level's depth, by its own walk (what C's `Level.mkData` bounds). -/
def depth : Level → Nat
  | .zero | .param _ | .mvar _ => 0
  | .succ u => depth u + 1
  | .max u v | .imax u v => max (depth u) (depth v) + 1

end Lvl

/-! ## The shared `bvar` pool (twin of `ConLeche.Expr.bvarPool`)

`bvarPool` is one static table of the first `bvarPoolSize` `bvar` nodes: a
closed top-level `def`, built once at module initialization and marked
persistent, so handing out `bvarPool[i]` costs a bounds check and a
borrowed read, with no allocation and no reference counting.  `mkBvar` is
the runtime `bvar` builder of the walks and decoders; it is
representation-transparent (`mkBvar_eq`, `@[simp]`).  Closed constants
such as `.bvar 0` keep the bare constructor: the compiler already lifts
them to persistent closed terms. -/

/-- Size of the static `bvar` pool. -/
def bvarPoolSize : Nat := 4096

@[inherit_doc bvarPoolSize]
def bvarPool : Array Expr := (Array.range bvarPoolSize).map Expr.bvar

/-- The `bvar` smart constructor: the pooled node below `bvarPoolSize`,
a fresh one above it.  Same value either way (`mkBvar_eq`). -/
@[inline] def mkBvar (i : Nat) : Expr :=
  if h : i < bvarPool.size then bvarPool[i] else .bvar i

@[simp] theorem mkBvar_eq (i : Nat) : mkBvar i = .bvar i := by
  unfold mkBvar
  split
  · simp [bvarPool]
  · rfl

namespace EO

/- The walks' memos compare nodes exactly: a walk's result keeps the binder
names of its input (the generator's output must equal the official
constants). -/
attribute [local instance 2000] instBEqExprExact

/-- The memo of a walk: node and offset to result. -/
abbrev Memo := Std.HashMap (Expr × Nat) Expr

/-- A walk's own empty memo, sized by the term's depth: an allocation of the
walk's own, so its first insert writes in place (a closed `{}` is one
shared constant, whose first insert copies the bucket array). -/
@[inline] def freshFor {α β : Type} [BEq α] [Hashable α] (e : Expr) : Std.HashMap α β :=
  Std.HashMap.emptyWithCapacity (e.approxDepth.toNat + 8)

@[inline] def isCompound : Expr → Bool
  | .app .. | .lam .. | .forallE .. | .letE .. | .mdata .. | .proj .. => true
  | _ => false

/-! ### The memo of the walks

con-leche's discipline (`ConLeche.Cached.ExprOpsC`, "The substitution
walks"): at every compound node past the cutoff the walk asks
`withExclusive` (`Lean.Kernel.InLean.Exclusive`) whether the node is exclusive; an
exclusive node cannot be reached twice and is descended with the memo
untouched, a shared one is probed and, on a miss, recorded.  The key is the
node's address packed with the binder offset (`pkey`), the table is created
at the first shared node, and an entry carries its node, its offset, its
value and the proof, so a hit is believed only after the pointer test
(`ptrDec`) and there is no table invariant.  The walks return a `Squash` of
the value with its proof against the plain descent beside the memo, so the
obligations of `withExclusive` and `withPtrAddr` are `Subsingleton.elim`. -/

/-- The packed key: the address over its 8-byte alignment, then the offset
modulo `2^16` in the low bits. -/
@[inline] def pkey (addr : USize) (c : Nat) : Nat :=
  (addr.toUInt64 / 8 * 65536 + (UInt64.ofNat c &&& 65535)).toNat

/-- A memo entry: the node, the offset, the value and its proof. -/
structure PEnt {β : Type} (s : Expr → Nat → β) where
  node : Expr
  depth : Nat
  val : β
  eq : val = s node depth

/-- A validated hit: the offsets compare equal and the stored node IS the
current one (by pointer at runtime). -/
@[inline] def PEnt.hit {β : Type} {s : Expr → Nat → β} {γ : Sort u} (p : PEnt s) (e : Expr)
    (c : Nat) (k : { r : β // r = s e c } → γ) (miss : Unit → γ) : γ :=
  if hd : p.depth = c then
    match ptrDec p.node e with
    | isTrue hn => k ⟨p.val, by rw [p.eq, hn, hd]⟩
    | isFalse _ => miss ()
  else miss ()

/-- The table's key: the packed `Nat` under a mixing hash. -/
structure PKey where
  val : Nat

instance : BEq PKey := ⟨fun a b => a.val == b.val⟩
instance : Hashable PKey := ⟨fun k => hash64 (UInt64.ofNat k.val)⟩

/-- The pointer-keyed memo: absent until the first shared compound node. -/
abbrev MemoXP {β : Type} (s : Expr → Nat → β) := Option (Std.HashMap PKey (PEnt s))

/-- A walk's result: the value, fixed by its proof, beside the memo. -/
abbrev ResXP {β : Type} (s : Expr → Nat → β) (e : Expr) (c : Nat) :=
  { r : β // r = s e c } × MemoXP s

@[inline] def MemoXP.insert {β : Type} {s : Expr → Nat → β} (memo : MemoXP s) (key : Nat)
    (p : PEnt s) : MemoXP s :=
  match memo with
  | none => some (({} : Std.HashMap PKey (PEnt s)).insert ⟨key⟩ p)
  | some m => some (m.insert ⟨key⟩ p)

/-- The shared-node step: the address read, the probe, the validated hit —
else the descent and the record under the key read before it. -/
@[inline] def MemoXP.shared {β : Type} {s : Expr → Nat → β} (memo : MemoXP s) (e : Expr)
    (c : Nat) (rec : Unit → Squash (ResXP s e c)) : Squash (ResXP s e c) :=
  withAddr e fun addr =>
  let key := pkey addr c
  match memo with
  | none => Squash.lift (rec ()) fun (⟨r, hr⟩, memo) =>
      Squash.mk (⟨r, hr⟩, memo.insert key ⟨e, c, r, hr⟩)
  | some m =>
    match m[(⟨key⟩ : PKey)]? with
    | some p => p.hit e c (fun r => Squash.mk (r, memo)) fun _ =>
        Squash.lift (rec ()) fun (⟨r, hr⟩, memo) =>
          Squash.mk (⟨r, hr⟩, memo.insert key ⟨e, c, r, hr⟩)
    | none => Squash.lift (rec ()) fun (⟨r, hr⟩, memo) =>
        Squash.mk (⟨r, hr⟩, memo.insert key ⟨e, c, r, hr⟩)

/-- The value of a walk's result (fixed by its subtype). -/
@[inline] def resVal {β : Type} {c : β} {M : Type} (s : Squash ({ r : β // r = c } × M)) : β :=
  Quotient.lift (fun p => p.1.1) (fun p q _ => by rw [p.1.2, q.1.2]) s

theorem resVal_eq {β : Type} {c : β} {M : Type} (s : Squash ({ r : β // r = c } × M)) :
    resVal s = c := by
  induction s using Quotient.ind with
  | _ p => exact p.1.2

/-! ### The offset map -/

/-- **The plain offset map**: `f e k` decides a node (`some r`), or the map
rebuilds it from its mapped children (offset `+1` under a binder). -/
def mapP (f : Expr → Nat → Option Expr) (e : Expr) (k : Nat) : Expr :=
  match f e k with
  | some r => r
  | none =>
    match e with
    | .app g a => e.updateApp! (mapP f g k) (mapP f a k)
    | .lam _ t b _ => e.updateLambdaE! (mapP f t k) (mapP f b (k + 1))
    | .forallE _ t b _ => e.updateForallE! (mapP f t k) (mapP f b (k + 1))
    | .letE _ t v b _ => e.updateLetE! (mapP f t k) (mapP f v k) (mapP f b (k + 1))
    | .mdata _ x => e.updateMData! (mapP f x k)
    | .proj _ _ x => e.updateProj! (mapP f x k)
    | _ => e

theorem mapP_some {f : Expr → Nat → Option Expr} {e : Expr} {k : Nat} {r : Expr}
    (h : f e k = some r) : mapP f e k = r := by
  rw [mapP.eq_def, h]

theorem mapP_leaf {f : Expr → Nat → Option Expr} {e : Expr} {k : Nat}
    (h : f e k = none) (hc : isCompound e = false) : mapP f e k = e := by
  rw [mapP.eq_def, h]; cases e <;> simp_all [isCompound]

theorem mapP_app {f : Expr → Nat → Option Expr} {g a : Expr} {k : Nat} (h : f (.app g a) k = none) :
    mapP f (.app g a) k = (Expr.app g a).updateApp! (mapP f g k) (mapP f a k) := by
  rw [mapP.eq_def, h]

theorem mapP_lam {f : Expr → Nat → Option Expr} {n t b bi} {k : Nat}
    (h : f (.lam n t b bi) k = none) :
    mapP f (.lam n t b bi) k = (Expr.lam n t b bi).updateLambdaE! (mapP f t k) (mapP f b (k + 1)) := by
  rw [mapP.eq_def, h]

theorem mapP_forallE {f : Expr → Nat → Option Expr} {n t b bi} {k : Nat}
    (h : f (.forallE n t b bi) k = none) :
    mapP f (.forallE n t b bi) k
      = (Expr.forallE n t b bi).updateForallE! (mapP f t k) (mapP f b (k + 1)) := by
  rw [mapP.eq_def, h]

theorem mapP_letE {f : Expr → Nat → Option Expr} {n t v b nd} {k : Nat}
    (h : f (.letE n t v b nd) k = none) :
    mapP f (.letE n t v b nd) k
      = (Expr.letE n t v b nd).updateLetE! (mapP f t k) (mapP f v k) (mapP f b (k + 1)) := by
  rw [mapP.eq_def, h]

theorem mapP_mdata {f : Expr → Nat → Option Expr} {m x} {k : Nat} (h : f (.mdata m x) k = none) :
    mapP f (.mdata m x) k = (Expr.mdata m x).updateMData! (mapP f x k) := by
  rw [mapP.eq_def, h]

theorem mapP_proj {f : Expr → Nat → Option Expr} {sn i x} {k : Nat} (h : f (.proj sn i x) k = none) :
    mapP f (.proj sn i x) k = (Expr.proj sn i x).updateProj! (mapP f x k) := by
  rw [mapP.eq_def, h]

/-- The child step of `mapX`: the callback (the cutoff), the compound test,
the exclusivity read. -/
@[inline] def enterMap (f : Expr → Nat → Option Expr) (memo : MemoXP (mapP f)) (e : @& Expr)
    (k : Nat) (rec : f e k = none → isCompound e = true → Squash (ResXP (mapP f) e k)) :
    Squash (ResXP (mapP f) e k) :=
  match h : f e k with
  | some r => Squash.mk (⟨r, (mapP_some h).symm⟩, memo)
  | none =>
    if hc : isCompound e then withExcl e fun excl =>
      if excl then rec h hc else memo.shared e k fun _ => rec h hc
    else Squash.mk (⟨e, (mapP_leaf h (by simpa using hc)).symm⟩, memo)

/-- **The memoised offset map**: the walk of `mapP f`, its node past the
callback. -/
@[specialize] def mapX (f : Expr → Nat → Option Expr) (memo : MemoXP (mapP f)) (e : @& Expr)
    (k : Nat) (h : f e k = none) (hc : isCompound e = true) :
    Squash (ResXP (mapP f) e k) :=
  match he : e with
  | .app g a =>
    enterMap f memo g k (fun h hc => mapX f memo g k h hc) |>.lift fun (⟨g', hg⟩, memo) =>
    enterMap f memo a k (fun h hc => mapX f memo a k h hc) |>.lift fun (⟨a', ha⟩, memo) =>
    Squash.mk (⟨e.updateApp! g' a', by rw [he, mapP_app h, hg, ha]⟩, memo)
  | .lam _ t b _ =>
    enterMap f memo t k (fun h hc => mapX f memo t k h hc) |>.lift fun (⟨t', ht⟩, memo) =>
    enterMap f memo b (k + 1) (fun h hc => mapX f memo b (k + 1) h hc) |>.lift fun (⟨b', hb⟩, memo) =>
    Squash.mk (⟨e.updateLambdaE! t' b', by rw [he, mapP_lam h, ht, hb]⟩, memo)
  | .forallE _ t b _ =>
    enterMap f memo t k (fun h hc => mapX f memo t k h hc) |>.lift fun (⟨t', ht⟩, memo) =>
    enterMap f memo b (k + 1) (fun h hc => mapX f memo b (k + 1) h hc) |>.lift fun (⟨b', hb⟩, memo) =>
    Squash.mk (⟨e.updateForallE! t' b', by rw [he, mapP_forallE h, ht, hb]⟩, memo)
  | .letE _ t v b _ =>
    enterMap f memo t k (fun h hc => mapX f memo t k h hc) |>.lift fun (⟨t', ht⟩, memo) =>
    enterMap f memo v k (fun h hc => mapX f memo v k h hc) |>.lift fun (⟨v', hv⟩, memo) =>
    enterMap f memo b (k + 1) (fun h hc => mapX f memo b (k + 1) h hc) |>.lift fun (⟨b', hb⟩, memo) =>
    Squash.mk (⟨e.updateLetE! t' v' b', by rw [he, mapP_letE h, ht, hv, hb]⟩, memo)
  | .mdata _ x =>
    enterMap f memo x k (fun h hc => mapX f memo x k h hc) |>.lift fun (⟨x', hx⟩, memo) =>
    Squash.mk (⟨e.updateMData! x', by rw [he, mapP_mdata h, hx]⟩, memo)
  | .proj _ _ x =>
    enterMap f memo x k (fun h hc => mapX f memo x k h hc) |>.lift fun (⟨x', hx⟩, memo) =>
    Squash.mk (⟨e.updateProj! x', by rw [he, mapP_proj h, hx]⟩, memo)
  | .bvar .. | .fvar .. | .mvar .. | .sort .. | .const .. | .lit .. =>
    absurd hc (by simp [isCompound])

/-- The offset map from offset `k`: the callback at the root, then the walk
(the root is never probed: it cannot be reached again). -/
@[inline] def mapOff (f : Expr → Nat → Option Expr) (e : Expr) (k : Nat) : Expr :=
  match h : f e k with
  | some r => r
  | none => if hc : isCompound e then resVal (mapX f none e k h hc) else e

theorem mapOff_eq (f : Expr → Nat → Option Expr) (e : Expr) (k : Nat) :
    mapOff f e k = mapP f e k := by
  unfold mapOff
  split
  · rename_i r h; exact (mapP_some h).symm
  · rename_i h
    split
    · exact resVal_eq _
    · rename_i hc; exact (mapP_leaf h (by simpa using hc)).symm

/-- Twin of `Expr.liftLooseBVars e s d`: loose `bvar i ≥ s` to `bvar (i + d)`. -/
def liftLooseBVars (e : Expr) (s d : Nat) : Expr :=
  if d == 0 || e.looseBVarRange ≤ s then e else
  (mapOff (fun x k =>
    if x.looseBVarRange ≤ s + k then some x else
    match x with
    | .bvar i => some (.bvar (i + d))
    | _ => none) e 0 )

/-- Twin of `Expr.lowerLooseBVars e s d`: loose `bvar i ≥ s` to `bvar (i - d)`. -/
def lowerLooseBVars (e : Expr) (s d : Nat) : Expr :=
  if d == 0 || e.looseBVarRange ≤ s then e else
  (mapOff (fun x k =>
    if x.looseBVarRange ≤ s + k then some x else
    match x with
    | .bvar i => some (.bvar (i - d))
    | _ => none) e 0 )

/-- The substitution of `n` values read by `get`: `bvar (k + j)` (`j < n`) to
`get j` lifted by `k`, above the substitution lowered by `n`. -/
@[inline] def instantiateBy (e : Expr) (n : Nat) (get : Nat → Expr) : Expr :=
  if n == 0 || !e.hasLooseBVars then e else
  (mapOff (fun x k =>
    if x.looseBVarRange ≤ k then some x else
    match x with
    | .bvar i =>
      if i < k then some x
      else if i - k < n then some (liftLooseBVars (get (i - k)) 0 k)
      else some (mkBvar (i - n))
    | _ => none) e 0 )

/-- Twin of `instantiateListC` (Lean's `instantiate`): `bvar (k + j)` to
`subst[j]` lifted by `k`, above the substitution lowered by its size. -/
def instantiate (e : Expr) (subst : Array Expr) : Expr :=
  instantiateBy e subst.size (fun j => subst[j]!)

/-- Twin of `instantiate1C`. -/
def instantiate1 (e v : Expr) : Expr := instantiateBy e 1 (fun _ => v)

/-- Twin of `instantiateRev`: `bvar 0` is the last element. -/
def instantiateRev (e : Expr) (subst : Array Expr) : Expr :=
  instantiateBy e subst.size (fun j => subst[subst.size - 1 - j]!)

/-- Lean's `instantiateRevRange e beg end subst`. -/
@[inline] def instantiateRevRange (e : Expr) (beg stop : Nat) (subst : Array Expr) : Expr :=
  instantiateRev e (subst.extract beg stop)

/-- The largest index a `bvar` node can carry: C's `lean_expr_mk_data`
panics at a range above `2^20 - 1`. -/
def maxBVarIdx : Nat := 1048574

/-- What `abstract` writes in place of an out-of-range `bvar`: a
metavariable, which no checker input has, so the result's `hasExprMVar`
reports it in O(1). -/
def rangePoison : Expr := .mvar ⟨`_inlean_range⟩

/-- Twin of `abstractRangeC` (Lean's `abstract`): the free variable
`xs[j]` to `bvar (k + n - 1 - j)` (`rangePoison` if that is out of range). -/
def abstract (e : Expr) (xs : Array Expr) : Expr :=
  if xs.isEmpty || !e.hasFVar then e else
  let n := xs.size
  let idx : Std.HashMap FVarId Nat := Id.run do
    let mut m : Std.HashMap FVarId Nat := {}
    for j in [0:n] do
      if let .fvar id := xs[j]! then
        if !m.contains id then m := m.insert id j
    return m
  (mapOff (fun x k =>
    if !x.hasFVar then some x else
    match x with
    | .fvar id => (idx[id]?).map fun j =>
      let i := k + n - 1 - j
      if i ≤ maxBVarIdx then mkBvar i else rangePoison
    | _ => none) e 0 )

/-- Lean's `abstractRange e n xs`. -/
@[inline] def abstractRange (e : Expr) (n : Nat) (xs : Array Expr) : Expr :=
  abstract e (xs.extract 0 n)

/-- The root of an interned free variable's name (`Lean.Kernel.InLean.StateC`):
the variable at depth `d` numbered `n` is named `fvRoot.d.n`. -/
def fvRoot : Name := `_inlean_fv

/-- An interned free variable's depth, read off its id. -/
@[inline] def fvDepth? (id : FVarId) : Option Nat :=
  match id.name with
  | .num (.num p d) _ => if p == fvRoot then some d else none
  | _ => none

/-- Twin of `abstractRangeC e d k`: every free variable at a depth `idx`
with `d ≤ idx < d + k` to `bvar (c + (d + k - 1 - idx))` at binder offset
`c` (`rangePoison` if that is out of range), whatever its type. -/
def abstractDepthsFrom (e : Expr) (d k c₀ : Nat) : Expr :=
  if k == 0 || !e.hasFVar then e else
  (mapOff (fun x c =>
    if !x.hasFVar then some x else
    match x with
    | .fvar id =>
      match fvDepth? id with
      | some idx =>
        if d ≤ idx ∧ idx < d + k then
          let i := c + (d + k - 1 - idx)
          some (if i ≤ maxBVarIdx then mkBvar i else rangePoison)
        else some x
      | none => some x
    | _ => none) e c₀ )

/-- `abstractDepthsFrom` at binder offset `0` (con-leche's `abstractRangeC e d k`). -/
@[inline] def abstractDepths (e : Expr) (d k : Nat) : Expr := abstractDepthsFrom e d k 0

/-- The level depth C's `Level.mkData` accepts. -/
def maxLevelDepth : Nat := 16777215

/-- The deepest of `us`, by their cached depths. -/
def maxDepthOf (us : List Level) : Nat := us.foldr (fun u m => max u.data.depth.toNat m) 0

/-- Substituting levels at most `md` deep into `u` stays within C's bound,
by `u`'s cached depth: the substitution adds at most `md`. -/
@[inline] def depthFits (md : Nat) (u : Level) : Bool := u.data.depth.toNat + md ≤ maxLevelDepth

/-- The `imax` chain `inferPisOutI stk v` builds stays within C's depth
bound, by cached depths: each `imax` adds at most one to the deepest level.
(`.succ u` is `depthFits 1 u`, one `imax u v` is `imaxChainFits [u] v`.) -/
def imaxChainFits (stk : List Level) (v : Level) : Bool :=
  maxDepthOf (v :: stk) + stk.length ≤ maxLevelDepth

/-- Twin of `instLevelParams`: the level parameters `ps` to `us` in every
`sort` and `const`, by con-leche's non-simplifying `Lvl.subst` (core's `Level.instantiateParams` compares by the opaque `Level.beq`).  A
node whose substituted level could pass C's depth bound becomes
`rangePoison`, which the checker's call sites report (`instLevelParamsChecked?`). -/
def instantiateLevelParams (e : Expr) (ps : List Name) (us : List Level) : Expr :=
  if ps.isEmpty || us.isEmpty || !e.hasLevelParam then e else
  let md := maxDepthOf us
  (mapOff (fun x _ =>
    if !x.hasLevelParam then some x else
    match x with
    | .sort u =>
      some (if depthFits md u then x.updateSort! (Lvl.subst ps us u) else rangePoison)
    | .const _ ls =>
      some (if ls.all (depthFits md) then x.updateConst! (ls.map (Lvl.subst ps us))
        else rangePoison)
    | _ => none) e 0 )

/-- `instantiateLevelParams`, `none` where it wrote `rangePoison` (a level
past C's depth bound, where C's `Level.mkData` would abort).  Checker terms
have no metavariable, so `hasExprMVar` reads the poison. -/
def instLevelParamsChecked? (e : Expr) (ps : List Name) (us : List Level) : Option Expr :=
  let r := instantiateLevelParams e ps us
  if r.hasExprMVar then none else some r

/-- `Lvl.subst` over a list of levels, `none` where a result could pass C's
depth bound. -/
def substLevelsChecked? (ps : List Name) (us : List Level) (ls : List Level) : Option (List Level) :=
  let md := maxDepthOf us
  if ls.all (depthFits md) then some (ls.map (Lvl.subst ps us)) else none

/-- The GENERATOR's level instantiation (unverified, `Lean.Kernel.InLean.IndGen`):
Lean's simplifying `Level.instantiateParams`, whose shapes the official
constants carry. -/
def instantiateLevelParamsGen (e : Expr) (ps : List Name) (us : List Level) : Expr :=
  if ps.isEmpty || us.isEmpty || !e.hasLevelParam then e else
  (mapOff (fun x _ =>
    if !x.hasLevelParam then some x else
    match x with
    | .sort u => some (x.updateSort! (u.instantiateParams ps us))
    | .const _ ls => some (x.updateConst! (ls.map (·.instantiateParams ps us)))
    | _ => none) e 0 )

/-- Generic memoised replacement (no offset; Lean's `Expr.replace`). -/
@[inline] def replace (f : Expr → Option Expr) (e : Expr) : Expr :=
  (mapOff (fun x _ => f x) e 0 )

/-- **The plain fold of a `Bool` property**: `p` decides a node (`some`
stops the descent), or the fold asks the children, left to right. -/
def anyP (p : Expr → Nat → Option Bool) (e : Expr) (k : Nat) : Bool :=
  match p e k with
  | some b => b
  | none =>
    match e with
    | .app g a => anyP p g k || anyP p a k
    | .lam _ t b _ => anyP p t k || anyP p b (k + 1)
    | .forallE _ t b _ => anyP p t k || anyP p b (k + 1)
    | .letE _ t v b _ => anyP p t k || anyP p v k || anyP p b (k + 1)
    | .mdata _ x => anyP p x k
    | .proj _ _ x => anyP p x k
    | _ => false

theorem anyP_some {p : Expr → Nat → Option Bool} {e : Expr} {k : Nat} {b : Bool}
    (h : p e k = some b) : anyP p e k = b := by
  rw [anyP.eq_def, h]

theorem anyP_leaf {p : Expr → Nat → Option Bool} {e : Expr} {k : Nat}
    (h : p e k = none) (hc : isCompound e = false) : anyP p e k = false := by
  rw [anyP.eq_def, h]; cases e <;> simp_all [isCompound]

theorem anyP_app {p : Expr → Nat → Option Bool} {g a : Expr} {k : Nat} (h : p (.app g a) k = none) :
    anyP p (.app g a) k = (anyP p g k || anyP p a k) := by
  rw [anyP.eq_def, h]

theorem anyP_lam {p : Expr → Nat → Option Bool} {n t b bi} {k : Nat}
    (h : p (.lam n t b bi) k = none) :
    anyP p (.lam n t b bi) k = (anyP p t k || anyP p b (k + 1)) := by
  rw [anyP.eq_def, h]

theorem anyP_forallE {p : Expr → Nat → Option Bool} {n t b bi} {k : Nat}
    (h : p (.forallE n t b bi) k = none) :
    anyP p (.forallE n t b bi) k = (anyP p t k || anyP p b (k + 1)) := by
  rw [anyP.eq_def, h]

theorem anyP_letE {p : Expr → Nat → Option Bool} {n t v b nd} {k : Nat}
    (h : p (.letE n t v b nd) k = none) :
    anyP p (.letE n t v b nd) k = (anyP p t k || anyP p v k || anyP p b (k + 1)) := by
  rw [anyP.eq_def, h]

theorem anyP_mdata {p : Expr → Nat → Option Bool} {m x} {k : Nat} (h : p (.mdata m x) k = none) :
    anyP p (.mdata m x) k = anyP p x k := by
  rw [anyP.eq_def, h]

theorem anyP_proj {p : Expr → Nat → Option Bool} {sn i x} {k : Nat} (h : p (.proj sn i x) k = none) :
    anyP p (.proj sn i x) k = anyP p x k := by
  rw [anyP.eq_def, h]

/-- The child step of `anyX`: the callback (the cutoff), the compound test,
the exclusivity read. -/
@[inline] def enterAny (p : Expr → Nat → Option Bool) (memo : MemoXP (anyP p)) (e : @& Expr)
    (k : Nat) (rec : p e k = none → isCompound e = true → Squash (ResXP (anyP p) e k)) :
    Squash (ResXP (anyP p) e k) :=
  match h : p e k with
  | some b => Squash.mk (⟨b, (anyP_some h).symm⟩, memo)
  | none =>
    if hc : isCompound e then withExcl e fun excl =>
      if excl then rec h hc else memo.shared e k fun _ => rec h hc
    else Squash.mk (⟨false, (anyP_leaf h (by simpa using hc)).symm⟩, memo)

/-- **The memoised fold**: the walk of `anyP p`, its node past the
callback; a `true` stops it. -/
@[specialize] def anyX (p : Expr → Nat → Option Bool) (memo : MemoXP (anyP p)) (e : @& Expr)
    (k : Nat) (h : p e k = none) (hc : isCompound e = true) :
    Squash (ResXP (anyP p) e k) :=
  match he : e with
  | .app g a =>
    enterAny p memo g k (fun h hc => anyX p memo g k h hc) |>.lift fun (⟨r₁, h₁⟩, memo) =>
    if hr : r₁ then Squash.mk (⟨true, by rw [anyP_app h, ← h₁, hr]; rfl⟩, memo) else
    enterAny p memo a k (fun h hc => anyX p memo a k h hc) |>.lift fun (⟨r₂, h₂⟩, memo) =>
    Squash.mk (⟨r₂, by rw [anyP_app h, ← h₁, ← h₂]; simp [hr]⟩, memo)
  | .lam _ t b _ =>
    enterAny p memo t k (fun h hc => anyX p memo t k h hc) |>.lift fun (⟨r₁, h₁⟩, memo) =>
    if hr : r₁ then Squash.mk (⟨true, by rw [anyP_lam h, ← h₁, hr]; rfl⟩, memo) else
    enterAny p memo b (k + 1) (fun h hc => anyX p memo b (k + 1) h hc) |>.lift fun (⟨r₂, h₂⟩, memo) =>
    Squash.mk (⟨r₂, by rw [anyP_lam h, ← h₁, ← h₂]; simp [hr]⟩, memo)
  | .forallE _ t b _ =>
    enterAny p memo t k (fun h hc => anyX p memo t k h hc) |>.lift fun (⟨r₁, h₁⟩, memo) =>
    if hr : r₁ then Squash.mk (⟨true, by rw [anyP_forallE h, ← h₁, hr]; rfl⟩, memo) else
    enterAny p memo b (k + 1) (fun h hc => anyX p memo b (k + 1) h hc) |>.lift fun (⟨r₂, h₂⟩, memo) =>
    Squash.mk (⟨r₂, by rw [anyP_forallE h, ← h₁, ← h₂]; simp [hr]⟩, memo)
  | .letE _ t v b _ =>
    enterAny p memo t k (fun h hc => anyX p memo t k h hc) |>.lift fun (⟨r₁, h₁⟩, memo) =>
    if hr : r₁ then Squash.mk (⟨true, by rw [anyP_letE h, ← h₁, hr]; rfl⟩, memo) else
    enterAny p memo v k (fun h hc => anyX p memo v k h hc) |>.lift fun (⟨r₂, h₂⟩, memo) =>
    if hr₂ : r₂ then Squash.mk (⟨true, by rw [anyP_letE h, ← h₁, ← h₂, hr₂]; simp⟩, memo) else
    enterAny p memo b (k + 1) (fun h hc => anyX p memo b (k + 1) h hc) |>.lift fun (⟨r₃, h₃⟩, memo) =>
    Squash.mk (⟨r₃, by rw [anyP_letE h, ← h₁, ← h₂, ← h₃]; simp [hr, hr₂]⟩, memo)
  | .mdata _ x =>
    enterAny p memo x k (fun h hc => anyX p memo x k h hc) |>.lift fun (⟨r, hx⟩, memo) =>
    Squash.mk (⟨r, by rw [anyP_mdata h, hx]⟩, memo)
  | .proj _ _ x =>
    enterAny p memo x k (fun h hc => anyX p memo x k h hc) |>.lift fun (⟨r, hx⟩, memo) =>
    Squash.mk (⟨r, by rw [anyP_proj h, hx]⟩, memo)
  | .bvar .. | .fvar .. | .mvar .. | .sort .. | .const .. | .lit .. =>
    absurd hc (by simp [isCompound])

/-- The fold from offset `k`: the callback at the root, then the walk. -/
@[inline] def anyNode (p : Expr → Nat → Option Bool) (e : Expr) (k : Nat) : Bool :=
  match h : p e k with
  | some b => b
  | none => if hc : isCompound e then resVal (anyX p none e k h hc) else false

theorem anyNode_eq (p : Expr → Nat → Option Bool) (e : Expr) (k : Nat) :
    anyNode p e k = anyP p e k := by
  unfold anyNode
  split
  · rename_i b h; exact (anyP_some h).symm
  · rename_i h
    split
    · exact resVal_eq _
    · rename_i hc; exact (anyP_leaf h (by simpa using hc)).symm

/-- Twin of `Expr.hasLooseBVarB i e`. -/
def hasLooseBVar (e : Expr) (i : Nat) : Bool :=
  (anyNode (fun x k =>
    if x.looseBVarRange ≤ i + k then some false else
    match x with
    | .bvar j => some (j == i + k)
    | _ => none) e 0 )

/-- Does some node satisfy `p` (Lean's `(e.find? p).isSome`, memoised)? -/
def any (p : Expr → Bool) (e : Expr) : Bool :=
  (anyNode (fun x _ => if p x then some true else none) e 0 )

/-- **In range, by the term alone**: every `bvar` index and level
depth below what C's `mkData` accepts, and no metavariable (so no
`rangePoison`).  It reads no cached field: it is the one check the proof takes
as the fact that an unverified term is in range. -/
def inRange (e : Expr) : Bool :=
  !(anyNode (fun x _ =>
    match x with
    | .bvar i => some (maxBVarIdx < i)
    | .mvar _ => some true
    | .sort u => some (16777215 < Lvl.depth u)
    | .const _ us => some (us.any fun u => 16777215 < Lvl.depth u)
    | _ => none) e 0 )

/-- The memoised fold collecting values of the nodes `pick` selects
(shared nodes visited once; `stop` cuts a subtree). -/
def collect (stop : Expr → Bool) (pick : Expr → Option α) (e : Expr) : Array α :=
  (go e (Std.HashSet.emptyWithCapacity (e.approxDepth.toNat + 8)) #[]).2
where
  go (e : Expr) (seen : Std.HashSet Expr) (acc : Array α) : Std.HashSet Expr × Array α :=
    if stop e then (seen, acc) else
    let acc := match pick e with
      | some a => acc.push a
      | none => acc
    if !isCompound e then (seen, acc) else
    if seen.contains e then (seen, acc) else
    let seen := seen.insert e
    match e with
    | .app g a => let (seen, acc) := go g seen acc; go a seen acc
    | .lam _ t b _ | .forallE _ t b _ => let (seen, acc) := go t seen acc; go b seen acc
    | .letE _ t v b _ =>
      let (seen, acc) := go t seen acc
      let (seen, acc) := go v seen acc
      go b seen acc
    | .mdata _ x | .proj _ _ x => go x seen acc
    | _ => (seen, acc)

/-- The free variables of `e`, each once (Lean's `collectFVars`). -/
def fvarIds (e : Expr) : Array FVarId :=
  let all := collect (fun x => !x.hasFVar) (fun | .fvar id => some id | _ => none) e
  (all.foldl (fun (s, acc) id => if s.contains id then (s, acc) else (s.insert id, acc.push id))
    (({} : Std.HashSet FVarId), #[])).2

/-- The constants of `e`, each once (Lean's `getUsedConstants`). -/
def usedConstants (e : Expr) : Array Name :=
  let all := collect (fun _ => false) (fun | .const n _ => some n | _ => none) e
  (all.foldl (fun (s, acc) n => if s.contains n then (s, acc) else (s.insert n, acc.push n))
    (({} : Std.HashSet Name), #[])).2

/-- The level parameters of `e`, each once (Lean's `CollectLevelParams`). -/
def levelParams (e : Expr) : Array Name :=
  let rec lvl : Level → Array Name → Array Name
    | .param n, acc => if acc.contains n then acc else acc.push n
    | .succ u, acc => lvl u acc
    | .max u v, acc | .imax u v, acc => lvl v (lvl u acc)
    | _, acc => acc
  let all := collect (fun x => !x.hasLevelParam)
    (fun | .sort u => some [u] | .const _ us => some us | _ => none) e
  all.foldl (fun acc us => us.foldl (fun acc u => lvl u acc) acc) #[]

/-- Lean's `Expr.headBeta`/`beta` on InLean's substitution. -/
def beta (f : Expr) (args : Array Expr) : Expr :=
  go f 0
where
  go (f : Expr) (i : Nat) : Expr :=
    if _h : i < args.size then
      match f with
      | .lam _ _ b _ => go b (i + 1)
      | _ => mkAppRange (instantiateRev f (args.extract 0 i)) i args.size args
    else instantiateRev f args
  termination_by args.size - i

end EO

end Lean.Kernel.InLean

/-! ## Dot-notation names for the call sites (InLean's own operations) -/

namespace Lean.Expr
open Lean.Kernel.InLean

/-- The head of an application spine, `mdata` read through (as con-leche's
`getAppFn` on the term without it). -/
def getAppFnT : Expr → Expr
  | .app f _ => getAppFnT f
  | .mdata _ e => getAppFnT e
  | e => e

/-- The spine's arguments, `mdata` read through. -/
def getAppArgsT (e : Expr) : Array Expr := (go e []).toArray
where
  go : Expr → List Expr → List Expr
    | .app f a, acc => go f (a :: acc)
    | .mdata _ e, acc => go e acc
    | _, acc => acc

/-- The spine's argument count, `mdata` read through. -/
def getAppNumArgsT : Expr → Nat
  | .app f _ => getAppNumArgsT f + 1
  | .mdata _ e => getAppNumArgsT e
  | _ => 0
@[inline] def inst1I (e v : Expr) : Expr := EO.instantiate1 e v
@[inline] def instI (e : Expr) (subst : Array Expr) : Expr := EO.instantiate e subst
@[inline] def instRevI (e : Expr) (subst : Array Expr) : Expr := EO.instantiateRev e subst
@[inline] def instRevRangeI (e : Expr) (beg stop : Nat) (subst : Array Expr) : Expr :=
  EO.instantiateRevRange e beg stop subst
@[inline] def abstractI (e : Expr) (xs : Array Expr) : Expr := EO.abstract e xs
@[inline] def abstractRangeI (e : Expr) (n : Nat) (xs : Array Expr) : Expr := EO.abstractRange e n xs
@[inline] def liftLooseBVarsI (e : Expr) (s d : Nat) : Expr := EO.liftLooseBVars e s d
@[inline] def lowerLooseBVarsI (e : Expr) (s d : Nat) : Expr := EO.lowerLooseBVars e s d
@[inline] def instLvlParamsI (e : Expr) (ps : List Name) (us : List Level) : Expr :=
  EO.instantiateLevelParams e ps us
/-- The generator's (official shapes; unverified). -/
@[inline] def instLvlParamsGenI (e : Expr) (ps : List Name) (us : List Level) : Expr :=
  EO.instantiateLevelParamsGen e ps us
@[inline] def hasLooseBVarI (e : Expr) (i : Nat) : Bool := EO.hasLooseBVar e i
@[inline] def replaceI (e : Expr) (f : Expr → Option Expr) : Expr := EO.replace f e
/-- `some e` iff some node satisfies `p` (the call sites read only
`isSome`/`isNone`). -/
@[inline] def findI? (e : Expr) (p : Expr → Bool) : Option Expr := if EO.any p e then some e else none
@[inline] def betaI (f : Expr) (args : Array Expr) : Expr := EO.beta f args
end Lean.Expr

namespace Lean.Kernel.InLean.EO

open Lean

attribute [local instance 2000] instBEqExprExact

/-- The memo probe and write-back around one compound node's step. -/
@[inline] def withMemo (e : Expr) (memo : Memo) (k : Memo → Expr × Memo) : Expr × Memo :=
  match memo[(e, 0)]? with
  | some r => (r, memo)
  | none => let (r, memo) := k memo; (r, memo.insert (e, 0) r)

/-- Every `mdata` node dropped (memoised, structural). -/
def stripMDataGo : Expr → Memo → Expr × Memo
  | .mdata _ x, memo => stripMDataGo x memo
  | e@(.app g a), memo => withMemo e memo fun memo =>
    let (g', memo) := stripMDataGo g memo
    let (a', memo) := stripMDataGo a memo
    (e.updateApp! g' a', memo)
  | e@(.lam _ t b _), memo => withMemo e memo fun memo =>
    let (t', memo) := stripMDataGo t memo
    let (b', memo) := stripMDataGo b memo
    (e.updateLambdaE! t' b', memo)
  | e@(.forallE _ t b _), memo => withMemo e memo fun memo =>
    let (t', memo) := stripMDataGo t memo
    let (b', memo) := stripMDataGo b memo
    (e.updateForallE! t' b', memo)
  | e@(.letE _ t v b _), memo => withMemo e memo fun memo =>
    let (t', memo) := stripMDataGo t memo
    let (v', memo) := stripMDataGo v memo
    let (b', memo) := stripMDataGo b memo
    (e.updateLetE! t' v' b', memo)
  | e@(.proj _ _ x), memo => withMemo e memo fun memo =>
    let (x', memo) := stripMDataGo x memo
    (e.updateProj! x', memo)
  | e, memo => (e, memo)

def stripMData (e : Expr) : Expr := (stripMDataGo e (freshFor e)).1

/-- Twin of `Expr.depthGo` (memoised), on the reading: an `mdata` node is read
through. -/
def depthGo : Expr → Std.HashMap Expr Nat → Nat × Std.HashMap Expr Nat
  | e, memo =>
    if !isCompound e then (1, memo) else
    match memo[e]? with
    | some r => (r, memo)
    | none =>
      let (r, memo) : Nat × Std.HashMap Expr Nat := match e with
        | .app f a =>
          let (d₁, memo) := depthGo f memo
          let (d₂, memo) := depthGo a memo
          (max d₁ d₂ + 1, memo)
        | .lam _ t b _ | .forallE _ t b _ =>
          let (d₁, memo) := depthGo t memo
          let (d₂, memo) := depthGo b memo
          (max d₁ d₂ + 1, memo)
        | .letE _ t v b _ =>
          let (d₁, memo) := depthGo t memo
          let (d₂, memo) := depthGo v memo
          let (d₃, memo) := depthGo b memo
          (max (max d₁ d₂) d₃ + 1, memo)
        | .mdata _ x => depthGo x memo
        | .proj _ _ x =>
          let (d, memo) := depthGo x memo
          (d + 1, memo)
        | _ => (1, memo)
      (r, memo.insert e r)

def depth (e : Expr) : Nat := (depthGo e (freshFor e)).1

/-- The memo probe and write-back around one compound node's hash. -/
@[inline] def withMemoH (e : Expr) (memo : Std.HashMap Expr UInt64)
    (k : Std.HashMap Expr UInt64 → UInt64 × Std.HashMap Expr UInt64) :
    UInt64 × Std.HashMap Expr UInt64 :=
  match memo[e]? with
  | some h => (h, memo)
  | none => let (h, memo) := k memo; (h, memo.insert e h)

/-- **A hash compatible with `Expr.clEq`**: binder names, infos, `nonDep` and
`mdata` not read (Lean's cached hash reads all but `mdata`; a leaf has none
and is hashed by it).  A memoised walk. -/
def clHashGo : Expr → Std.HashMap Expr UInt64 → UInt64 × Std.HashMap Expr UInt64
  | .mdata _ x, memo => clHashGo x memo
  | e@(.app f a), memo => withMemoH e memo fun memo =>
    let (h₁, memo) := clHashGo f memo
    let (h₂, memo) := clHashGo a memo
    (mixHash 5 (mixHash h₁ h₂), memo)
  | e@(.lam _ t b _), memo => withMemoH e memo fun memo =>
    let (h₁, memo) := clHashGo t memo
    let (h₂, memo) := clHashGo b memo
    (mixHash 6 (mixHash h₁ h₂), memo)
  | e@(.forallE _ t b _), memo => withMemoH e memo fun memo =>
    let (h₁, memo) := clHashGo t memo
    let (h₂, memo) := clHashGo b memo
    (mixHash 7 (mixHash h₁ h₂), memo)
  | e@(.letE _ t v b _), memo => withMemoH e memo fun memo =>
    let (h₁, memo) := clHashGo t memo
    let (h₂, memo) := clHashGo v memo
    let (h₃, memo) := clHashGo b memo
    (mixHash 8 (mixHash h₁ (mixHash h₂ h₃)), memo)
  | e@(.proj s i x), memo => withMemoH e memo fun memo =>
    let (h₁, memo) := clHashGo x memo
    (mixHash 11 (mixHash (hash s) (mixHash (hash i) h₁)), memo)
  | e, memo => (hash e, memo)

def clHash (e : Expr) : UInt64 := (clHashGo e (freshFor e)).1

end Lean.Kernel.InLean.EO


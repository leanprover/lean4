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

Core's opaque
C++ operations — `instantiate`, `instantiate1`, `instantiateRev(Range)`,
`abstract(Range)`, `lift`/`lowerLooseBVars`, `hasLooseBVar`, and the
`implemented_by` traversals (`Expr.replace`, `Expr.find?`,
`collectFVars`, `getUsedConstants`, the level-parameter collector) — are
replaced by Lean-defined, memoised structural walks: twins of
`ConLeche/Cached/ExprOpsC.lean`'s substitutions (`instantiate1C`,
`instantiateListC`, `instantiateRev`, `abstract1C`, `abstractRangeC`,
`instLevelParams`) over `Lean.Expr`'s six binder-bearing constructors.

**The memo.**  con-leche's walks memoise exactly the nodes the runtime
reports shared (`withExclusive`, its one `unsafe`-implemented primitive);
InLean may add no `unsafe` code, so every compound node is memoised, keyed
by the node and the binder offset under the lawful pointer-first equality
(`Lean/Kernel/InLean/ExprEq.lean`) — a structural recursion, no fuel needed.

**The cutoffs** read Lean's cached fields (`looseBVarRange`, `hasFVar`,
`hasLevelParam`), as con-leche's read its computed `data` word.  Lean
computes them in C; the Lean bodies of `Expr.mkData`, `Expr.mkAppData` and
`Level.mkData` state what C computes.  Lean does not
saturate the range: a node above `2^20 - 1` loose variables aborts the
process ("too many bound variables").  So the one walk here that can grow
indices past a term's own, `abstract`, writes `rangePoison` instead of an
out-of-range `bvar`, and its checker call sites error on it in O(1)
(`InLean.abstractChecked`, `State.lean`).
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

namespace EO

/-- The memo of a walk: node and offset to result. -/
abbrev Memo := Std.HashMap (Expr × Nat) Expr

@[inline] def isCompound : Expr → Bool
  | .app .. | .lam .. | .forallE .. | .letE .. | .mdata .. | .proj .. => true
  | _ => false

/-- **The memoised offset map**: `f e k` decides a node (`some r`) or
lets the walk descend; every compound node's result is memoised under
`(node, offset)`.  Structural. -/
def mapOff (f : Expr → Nat → Option Expr) : Expr → Nat → Memo → Expr × Memo
  | e, k, memo =>
    match f e k with
    | some r => (r, memo)
    | none =>
      if !isCompound e then (e, memo) else
      match memo[(e, k)]? with
      | some r => (r, memo)
      | none =>
        let (r, memo) : Expr × Memo := match e with
          | .app g a =>
            let (g', memo) := mapOff f g k memo
            let (a', memo) := mapOff f a k memo
            (e.updateApp! g' a', memo)
          | .lam _ t b _ =>
            let (t', memo) := mapOff f t k memo
            let (b', memo) := mapOff f b (k + 1) memo
            (e.updateLambdaE! t' b', memo)
          | .forallE _ t b _ =>
            let (t', memo) := mapOff f t k memo
            let (b', memo) := mapOff f b (k + 1) memo
            (e.updateForallE! t' b', memo)
          | .letE _ t v b _ =>
            let (t', memo) := mapOff f t k memo
            let (v', memo) := mapOff f v k memo
            let (b', memo) := mapOff f b (k + 1) memo
            (e.updateLetE! t' v' b', memo)
          | .mdata _ x =>
            let (x', memo) := mapOff f x k memo
            (e.updateMData! x', memo)
          | .proj _ _ x =>
            let (x', memo) := mapOff f x k memo
            (e.updateProj! x', memo)
          | _ => (e, memo)
        (r, memo.insert (e, k) r)

/-- Twin of `Expr.liftLooseBVars e s d`: loose `bvar i ≥ s` to `bvar (i + d)`. -/
def liftLooseBVars (e : Expr) (s d : Nat) : Expr :=
  if d == 0 || e.looseBVarRange ≤ s then e else
  (mapOff (fun x k =>
    if x.looseBVarRange ≤ s + k then some x else
    match x with
    | .bvar i => some (.bvar (i + d))
    | _ => none) e 0 {}).1

/-- Twin of `Expr.lowerLooseBVars e s d`: loose `bvar i ≥ s` to `bvar (i - d)`. -/
def lowerLooseBVars (e : Expr) (s d : Nat) : Expr :=
  if d == 0 || e.looseBVarRange ≤ s then e else
  (mapOff (fun x k =>
    if x.looseBVarRange ≤ s + k then some x else
    match x with
    | .bvar i => some (.bvar (i - d))
    | _ => none) e 0 {}).1

/-- Twin of `instantiateListC` (Lean's `instantiate`): `bvar (k + j)` to
`subst[j]` lifted by `k`, above the substitution lowered by its size. -/
def instantiate (e : Expr) (subst : Array Expr) : Expr :=
  let n := subst.size
  if n == 0 || !e.hasLooseBVars then e else
  (mapOff (fun x k =>
    if x.looseBVarRange ≤ k then some x else
    match x with
    | .bvar i =>
      if i < k then some x
      else if i - k < n then some (liftLooseBVars (subst[i - k]!) 0 k)
      else some (.bvar (i - n))
    | _ => none) e 0 {}).1

/-- Twin of `instantiate1C`. -/
@[inline] def instantiate1 (e v : Expr) : Expr := instantiate e #[v]

/-- Twin of `instantiateRev`: `bvar 0` is the last element. -/
@[inline] def instantiateRev (e : Expr) (subst : Array Expr) : Expr := instantiate e subst.reverse

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
      if i ≤ maxBVarIdx then .bvar i else rangePoison
    | _ => none) e 0 {}).1

/-- Lean's `abstractRange e n xs`. -/
@[inline] def abstractRange (e : Expr) (n : Nat) (xs : Array Expr) : Expr :=
  abstract e (xs.extract 0 n)

/-- The root of an interned free variable's name (`Lean/Kernel/InLean/StateC.lean`):
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
          some (if i ≤ maxBVarIdx then .bvar i else rangePoison)
        else some x
      | none => some x
    | _ => none) e c₀ {}).1

/-- `abstractDepthsFrom` at binder offset `0` (con-leche's `abstractRangeC e d k`). -/
@[inline] def abstractDepths (e : Expr) (d k : Nat) : Expr := abstractDepthsFrom e d k 0

/-- Twin of `instLevelParams`: the level parameters `ps` to `us` in every
`sort` and `const`, by con-leche's non-simplifying `Lvl.subst` (core's
`Level.instantiateParams` compares by the opaque `Level.beq`). -/
def instantiateLevelParams (e : Expr) (ps : List Name) (us : List Level) : Expr :=
  if ps.isEmpty || us.isEmpty || !e.hasLevelParam then e else
  (mapOff (fun x _ =>
    if !x.hasLevelParam then some x else
    match x with
    | .sort u => some (x.updateSort! (Lvl.subst ps us u))
    | .const _ ls => some (x.updateConst! (ls.map (Lvl.subst ps us)))
    | _ => none) e 0 {}).1

/-- The GENERATOR's level instantiation (unverified, `Lean/Kernel/InLean/IndGen.lean`):
Lean's simplifying `Level.instantiateParams`, whose shapes the official
constants carry. -/
def instantiateLevelParamsGen (e : Expr) (ps : List Name) (us : List Level) : Expr :=
  if ps.isEmpty || us.isEmpty || !e.hasLevelParam then e else
  (mapOff (fun x _ =>
    if !x.hasLevelParam then some x else
    match x with
    | .sort u => some (x.updateSort! (u.instantiateParams ps us))
    | .const _ ls => some (x.updateConst! (ls.map (·.instantiateParams ps us)))
    | _ => none) e 0 {}).1

/-- Generic memoised replacement (no offset; Lean's `Expr.replace`). -/
@[inline] def replace (f : Expr → Option Expr) (e : Expr) : Expr :=
  (mapOff (fun x _ => f x) e 0 {}).1

/-- The memoised fold of a `Bool` property over every node (shared nodes
visited once): `some` stops the descent at a node. -/
def anyNode (p : Expr → Nat → Option Bool) : Expr → Nat → Std.HashMap (Expr × Nat) Bool →
    Bool × Std.HashMap (Expr × Nat) Bool
  | e, k, memo =>
    match p e k with
    | some b => (b, memo)
    | none =>
      if !isCompound e then (false, memo) else
      match memo[(e, k)]? with
      | some b => (b, memo)
      | none =>
        let (r, memo) : Bool × Std.HashMap (Expr × Nat) Bool := match e with
          | .app g a =>
            let (b, memo) := anyNode p g k memo
            if b then (true, memo) else anyNode p a k memo
          | .lam _ t b _ | .forallE _ t b _ =>
            let (r, memo) := anyNode p t k memo
            if r then (true, memo) else anyNode p b (k + 1) memo
          | .letE _ t v b _ =>
            let (r, memo) := anyNode p t k memo
            if r then (true, memo) else
            let (r, memo) := anyNode p v k memo
            if r then (true, memo) else anyNode p b (k + 1) memo
          | .mdata _ x | .proj _ _ x => anyNode p x k memo
          | _ => (false, memo)
        (r, memo.insert (e, k) r)

/-- Twin of `Expr.hasLooseBVarB i e`. -/
def hasLooseBVar (e : Expr) (i : Nat) : Bool :=
  (anyNode (fun x k =>
    if x.looseBVarRange ≤ i + k then some false else
    match x with
    | .bvar j => some (j == i + k)
    | _ => none) e 0 {}).1

/-- Does some node satisfy `p` (Lean's `(e.find? p).isSome`, memoised)? -/
def any (p : Expr → Bool) (e : Expr) : Bool :=
  (anyNode (fun x _ => if p x then some true else none) e 0 {}).1

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
    | _ => none) e 0 {}).1

/-- The memoised fold collecting values of the nodes `pick` selects
(shared nodes visited once; `stop` cuts a subtree). -/
def collect (stop : Expr → Bool) (pick : Expr → Option α) (e : Expr) : Array α :=
  (go e ({} : Std.HashSet Expr) #[]).2
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

def stripMData (e : Expr) : Expr := (stripMDataGo e {}).1

/-- Twin of `Expr.depthGo` (memoised). -/
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
        | .proj _ _ x | .mdata _ x =>
          let (d, memo) := depthGo x memo
          (d + 1, memo)
        | _ => (1, memo)
      (r, memo.insert e r)

def depth (e : Expr) : Nat := (depthGo e {}).1

end Lean.Kernel.InLean.EO

namespace Lean.Kernel.InLean.EO

open Lean

/-- **Alpha-equivalence** (binder names and infos, a `let`'s `nonDep`
ignored; everything else exact): con-leche's expression equality, whose
terms carry no binder names, and official's C++ `operator==`.  A
memoised pair walk, pointer-first. -/
def alphaEqGo : Expr → Expr → Std.HashMap (Expr × Expr) Bool → Bool × Std.HashMap (Expr × Expr) Bool
  | a, b, memo =>
    if Expr.beqI a b then (true, memo) else
    match memo[(a, b)]? with
    | some r => (r, memo)
    | none =>
      let (r, memo) : Bool × Std.HashMap (Expr × Expr) Bool := match a, b with
        | .app f x, .app g y =>
          let (r, memo) := alphaEqGo f g memo
          if r then alphaEqGo x y memo else (false, memo)
        | .lam _ t c _, .lam _ t' c' _ | .forallE _ t c _, .forallE _ t' c' _ =>
          let (r, memo) := alphaEqGo t t' memo
          if r then alphaEqGo c c' memo else (false, memo)
        | .letE _ t v c _, .letE _ t' v' c' _ =>
          let (r, memo) := alphaEqGo t t' memo
          if !r then (false, memo) else
          let (r, memo) := alphaEqGo v v' memo
          if r then alphaEqGo c c' memo else (false, memo)
        | .proj s i x, .proj s' i' x' =>
          if s == s' && i == i' then alphaEqGo x x' memo else (false, memo)
        | _, _ => (false, memo)
      (r, memo.insert (a, b) r)

/-- Alpha-equivalence up to `mdata` (both sides stripped first, so
no `KVMap`/`Syntax` equality — core's `Syntax.structEq` is opaque — is
consulted; con-leche's terms carry no `mdata`). -/
def alphaEq (a b : Expr) : Bool := (alphaEqGo (stripMData a) (stripMData b) {}).1

end Lean.Kernel.InLean.EO

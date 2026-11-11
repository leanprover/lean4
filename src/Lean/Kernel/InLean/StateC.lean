/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/
module

prelude

public import Lean.Kernel.InLean.Basic
public import Lean.Kernel.InLean.ExprEq

/-!
# InLean: the per-declaration state and its operation wrappers

Twin of `ConLeche.Cached.StateC`: the memo caches of the five entry
points (the plain tower's in their own fields, the eager tower's in
`eagerMemos`), the stored-constant caches, the level-operation memos and
the bulk-instantiation memo, each written in the linear-update discipline
(detach a component from the record before mutating it); `CheckCM` is
con-leche's monad, `StateT CState CheckM`.

**Free variables.**  con-leche's free variable is a de Bruijn level and
its type, both in the node (`.fvar d ty`).  A `Lean.Expr` free variable is
an id, so the pair is interned per declaration: the id's name is
`fvRoot.d.n` — the depth `d` readable from the id alone, so scope checks
stay pure (`Expr.wscopedBC`) — and `n` numbers the pair's class: types equal
by `Expr.clEq` (what con-leche's type would be equal for) share it, and
`CState.fvTys[n]` is the class's first type.  So a term opened twice at the
same depth with the same type is the same term, as in con-leche.
-/

@[expose] public section

namespace Lean.Kernel.InLean

open Lean

/-! ## The state -/

/-- Twin of `ModeMemos` (keys by `Expr.keyEq`, `EKey`). -/
structure ModeMemos where
  whnfCoreC : Std.HashMap EKey Expr := {}
  whnfCoreCheapC : Std.HashMap EKey Expr := {}
  whnfC : Std.HashMap EKey Expr := {}
  inferC : Std.HashMap EKey Expr := {}
  inferIOC : Std.HashMap EKey Expr := {}
  defeqC : Std.HashMap (EKey × EKey) Bool := {}

/-- Twin of `CState`, with the free-variable table. -/
structure CState where
  constTyAt : Std.HashMap (Name × List Level) Expr := {}
  constValAt : Std.HashMap (Name × List Level) Expr := {}
  ruleRhsAt : Std.HashMap (Name × Name × List Level) Expr := {}
  whnfCoreC : Std.HashMap EKey Expr := {}
  whnfCoreCheapC : Std.HashMap EKey Expr := {}
  whnfC : Std.HashMap EKey Expr := {}
  inferC : Std.HashMap EKey Expr := {}
  inferIOC : Std.HashMap EKey Expr := {}
  defeqC : Std.HashMap (EKey × EKey) Bool := {}
  lsimpC : Std.HashMap Level Level := {}
  eqvC : Std.HashMap (Level × Level) Bool := {}
  instC : Std.HashMap InstKey Expr := {}
  eagerMemos : ModeMemos := {}
  /-- `(depth, type)` ↦ the variable's number, by `keyEq` (the fast path). -/
  fvSeen : Std.HashMap (Nat × EKey) Nat := {}
  /-- `(depth, clHash type)` ↦ the numbers of that hash, each a distinct
  `clEq`-class of types. -/
  fvCls : Std.HashMap (Nat × UInt64) (List Nat) := {}
  /-- Per number: the free variable's type (its class's first member). -/
  fvTys : Array Expr := #[]

instance : Inhabited CState := ⟨{}⟩

/-- Twin of `instCCapC`. -/
def instCCapC : Nat := 32000000

/-- Twin of `CheckCM`. -/
abbrev CheckCM := StateT CState CheckM

/-- Twin of `peelFuel`. -/
def peelFuel : Nat := 16777216

@[inline] def peelFuelM : CheckCM Nat := pure peelFuel

/-! ## Free variables -/

/-- The id of pair number `n` at depth `d`. -/
@[inline] def fvId (d n : Nat) : FVarId := ⟨.num (.num EO.fvRoot d) n⟩

/-- An interned id's depth and number. -/
@[inline] def fvParts? (id : FVarId) : Option (Nat × Nat) :=
  match id.name with
  | .num (.num p d) n => if p == EO.fvRoot then some (d, n) else none
  | _ => none

/-- **Twin of the node `.fvar d ty`**: the interned free variable at depth
`d` of type `ty`.  One number per depth and `Expr.clEq`-class of the type
(con-leche's node `.fvar d ty` is one value per depth and type, and `clEq`
equal types stand for one con-leche type): a `keyEq` hit is the fast path,
a miss looks the class up under `EO.clHash`. -/
def mkFVarM (d : Nat) (ty : Expr) : CheckCM Expr :=
  modifyGet fun s =>
    match s.fvSeen[(d, EKey.mk ty)]? with
    | some n => (.fvar (fvId d n), s)
    | none =>
      let h := EO.clHash ty
      let seen := s.fvSeen
      let cls := s.fvCls
      let tys := s.fvTys
      let s := { s with fvSeen := {}, fvCls := {}, fvTys := #[] }
      let cands := cls.getD (d, h) []
      match cands.find? (fun n => Expr.clEq (tys[n]?.getD ty) ty) with
      | some n =>
        (.fvar (fvId d n), { s with fvSeen := seen.insert (d, EKey.mk ty) n, fvCls := cls,
                                    fvTys := tys })
      | none =>
        let n := tys.size
        (.fvar (fvId d n), { s with fvSeen := seen.insert (d, EKey.mk ty) n,
                                    fvCls := cls.insert (d, h) (n :: cands), fvTys := tys.push ty })

/-- An interned free variable's type (con-leche reads it off the node). -/
def fvarTypeM? (id : FVarId) : CheckCM (Option Expr) := do
  match fvParts? id with
  | some (_, n) => return (← get).fvTys[n]?
  | none => return none

/-- An interned free variable's depth. -/
@[inline] def fvarDepth? (id : FVarId) : Option Nat := EO.fvDepth? id

/-! ## Syntactic operations (the `*M` wrappers) -/

/-- Twin of `inst1M`. -/
@[inline] def inst1M (e v : Expr) : CheckCM Expr := pure (e.inst1I v)

/-- Twin of `instListM`: bulk instantiation (innermost first) under the
persistent result memo, keyed by the term and the values. -/
def instListM (e : Expr) (vs : List Expr) : CheckCM Expr :=
  modifyGet fun s =>
    if !e.hasLooseBVars then (e, s)
    else
      match s.instC[InstKey.mk e vs]? with
      | some r => (r, s)
      | none =>
        let mp := s.instC
        let s := { s with instC := {} }
        let mp := if mp.size < instCCapC then mp else {}
        let r := e.instI vs.toArray
        (r, { s with instC := mp.insert (InstKey.mk e vs) r })

/-- Twin of `instListRevM`. -/
@[inline] def instListRevM (e : Expr) (vs : Array Expr) : CheckCM Expr :=
  pure (e.instRevI vs)

/-- **Twin of `abstract1M`/`abstractRangeM`**: the free variables at depths
`d … d + k - 1` replaced by the loose bound variables.  An index past
C's bound is an error, where C's `Expr.mkData` would abort (checker terms
have no metavariable, so `hasExprMVar` reads `EO.rangePoison`). -/
def abstractRangeM (e : Expr) (d k : Nat) : CheckCM Expr := do
  let r := EO.abstractDepths e d k
  if r.hasExprMVar then throw (.internal "too many bound variables")
  return r

@[inline] def abstract1M (e : Expr) (d : Nat) : CheckCM Expr := abstractRangeM e d 1

/-- Twin of `mkAppNM`. -/
@[inline] def mkAppNM (f : Expr) (args : List Expr) : CheckCM Expr :=
  pure (mkAppN f args.toArray)

/-- Twin of `instLevelParamsM` (con-leche's non-simplifying substitution).  A
level past C's depth bound is an error, where C's `Level.mkData` would abort. -/
@[inline] def instLevelParamsM (ks : List Name) (us : List Level) (e : Expr) : CheckCM Expr :=
  match EO.instLevelParamsChecked? e ks us with
  | some r => pure r
  | none => throw (.internal "universe level too deep")

/-- Twin of `substLevelTreesM` (the depth bound as `instLevelParamsM`'s). -/
@[inline] def substLevelTreesM (ks : List Name) (us : List Level) (ls : List Level) :
    CheckCM (List Level) :=
  match EO.substLevelsChecked? ks us ls with
  | some r => pure r
  | none => throw (.internal "universe level too deep")

/-! ## Level operations -/

/-- Twin of `isEquivLM`. -/
def isEquivLM (l r : Level) : CheckCM (Option Bool) :=
  if l == r then pure (some true) else
  modifyGet fun s =>
    match s.eqvC[(l, r)]? with
    | some b => (some b, s)
    | none =>
      let mp := s.lsimpC
      let ec := s.eqvC
      let s := { s with lsimpC := {}, eqvC := {} }
      let (ls, mp) :=
        match mp[l]? with
        | some x => (x, mp)
        | none => let x := Lvl.simplify l; (x, mp.insert l x)
      let (rs, mp) :=
        match mp[r]? with
        | some x => (x, mp)
        | none => let x := Lvl.simplify r; (x, mp.insert r x)
      if ls == rs then
        (some true, { s with lsimpC := mp, eqvC := ec.insert (l, r) true })
      else
        match Lvl.leqCore Lvl.defaultFuel ls rs 0 with
        | some false =>
          (some false, { s with lsimpC := mp, eqvC := ec.insert (l, r) false })
        | some true =>
          match Lvl.leqCore Lvl.defaultFuel rs ls 0 with
          | some b => (some b, { s with lsimpC := mp, eqvC := ec.insert (l, r) b })
          | none => (none, { s with lsimpC := mp, eqvC := ec })
        | none => (none, { s with lsimpC := mp, eqvC := ec })

/-- Twin of `isEquivListLM`. -/
def isEquivListLM : List Level → List Level → CheckCM (Option Bool)
  | [], [] => pure (some true)
  | l :: ls, r :: rs => do
    match ← isEquivLM l r with
    | none => pure none
    | some false => pure (some false)
    | some true => isEquivListLM ls rs
  | _, _ => pure (some false)

/-- Twin of `liftFueled`: an exhausted level comparison is a decline. -/
def liftFueled (what : String) : Option α → CheckCM α
  | some a => pure a
  | none => throw (.notImplemented s!"resource limit: fuel exhausted: {what}")

/-! ## The eager tower's memos -/

/-- Twin of `CState.flushed`. -/
def CState.flushed (s : CState) : CState :=
  { s with
      constTyAt := {}, constValAt := {}, ruleRhsAt := {},
      whnfCoreC := {}, whnfCoreCheapC := {}, whnfC := {}, inferC := {}, inferIOC := {},
      defeqC := {}, instC := {}, eagerMemos := {} }

/-- Twin of `flushC`. -/
def flushC : CheckCM Unit := modify (·.flushed)

/-- Twin of `CState.modeMemos`. -/
def CState.modeMemos (s : CState) : ModeMemos :=
  ⟨s.whnfCoreC, s.whnfCoreCheapC, s.whnfC, s.inferC, s.inferIOC, s.defeqC⟩

/-- Twin of `CState.enterEager`. -/
def CState.enterEager (eager : Bool) (s : CState) : Option ModeMemos × CState :=
  if eager then (none, s) else
  (some s.modeMemos,
   { s with whnfCoreC := s.eagerMemos.whnfCoreC, whnfCoreCheapC := s.eagerMemos.whnfCoreCheapC,
            whnfC := s.eagerMemos.whnfC, inferC := s.eagerMemos.inferC,
            inferIOC := s.eagerMemos.inferIOC, defeqC := s.eagerMemos.defeqC,
            eagerMemos := {} })

/-- Twin of `CState.leaveEager`. -/
def CState.leaveEager (s : CState) : Option ModeMemos → CState
  | none => s
  | some saved =>
    { s with eagerMemos := s.modeMemos,
             whnfCoreC := saved.whnfCoreC, whnfCoreCheapC := saved.whnfCoreCheapC,
             whnfC := saved.whnfC, inferC := saved.inferC, inferIOC := saved.inferIOC,
             defeqC := saved.defeqC }

/-- Twin of `withEagerMemos`. -/
@[inline] def withEagerMemos (eager : Bool) (x : CheckCM α) : CheckCM α := do
  let saved ← modifyGet (CState.enterEager eager)
  let r ← x
  modify (·.leaveEager saved)
  pure r

end Lean.Kernel.InLean

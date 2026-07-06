import Lean

/-!
Fine-grained `synthPendingDepth` handling in the type-class resolution cache
(`SynthInstanceCacheKey.synthPendingDepth : Option Nat`).

Cache entries whose synthesis never reached a `synthPending` decision are depth-invariant
and shared across `synthPendingDepth` levels. Entries whose synthesis did reach one
(including giving up at `maxSynthPendingDepth`) remain keyed by their exact depth,
preserving the fix for issue #2522.

`Meta.synthPending` fires when unification is stuck on a pending instance metavariable,
e.g. a class projection applied to an unassigned instance mvar. The tests below construct
pending mvars by hand and simulate nested queries by setting `synthPendingDepth` directly.
The taint tests use a *local* instance because local instances are candidates regardless
of discrimination-tree keys, so a stuck projection in its type meets the rigid goal during
`tryResolve`.
-/

open Lean Meta

structure Wr (α : Type) : Type

class LeafT (α : Type) where T : Type
instance iLeafT : LeafT (Wr Nat) := ⟨Nat⟩

class Out (α : Type) (β : outParam Type) where
instance iOut : Out (Wr Nat) Nat := ⟨⟩

class Root (α : Type) where

def wrNat : Expr := mkApp (mkConst ``Wr) (mkConst ``Nat)
def leafTWr : Expr := mkApp (mkConst ``LeafT) wrNat
def projT (h : Expr) : Expr := mkApp2 (mkConst ``LeafT.T) wrNat h
def rootNat : Expr := mkApp (mkConst ``Root) (mkConst ``Nat)

def withTCTrace (x : MetaM α) : MetaM α :=
  withOptions (fun o =>
    (o.setBool `trace.Meta.synthInstance.cache true).setBool `trace.Meta.synthPending true) x

def atDepth (d : Nat) (x : MetaM α) : MetaM α :=
  withReader (fun ctx : Meta.Context => { ctx with synthPendingDepth := d }) x

set_option maxSynthPendingDepth 1

/-!
`LeafT (Wr Nat)` synthesis never reaches a `synthPending` decision, so its cache entry is
depth-invariant: computed at depth 0, it is reused at depths 1 and 2.
-/
/--
trace: [Meta.synthInstance.cache] new: LeafT (Wr Nat)
[Meta.synthInstance.cache] cached (synthPendingDepth := 1): LeafT (Wr Nat)
[Meta.synthInstance.cache] cached (synthPendingDepth := 2): LeafT (Wr Nat)
-/
#guard_msgs in
run_meta withTCTrace do
  discard <| synthInstance? leafTWr
  discard <| atDepth 1 do synthInstance? leafTWr
  discard <| atDepth 2 do synthInstance? leafTWr

/-!
A query with a stuck projection in an `outParam` position: the search itself is
depth-invariant (the out-param is replaced by a fresh mvar before the search), and the
depth-sensitive `synthPending` happens while assigning the out-params to the caller's
arguments, which is re-run on every cache hit. Hence the `Out` entry is shared with the
depth-1 query, and the nested `LeafT (Wr Nat)` query (depth 1 first, then depth 2 on the
cache hit) reuses the depth-invariant entry as well.
-/
/--
trace: [Meta.synthInstance.cache] new: Out (Wr Nat) (LeafT.T (Wr Nat))
[Meta.synthPending] synthPending ?m.1
[Meta.synthInstance.cache] new (synthPendingDepth := 1): LeafT (Wr Nat)
[Meta.synthInstance.cache] cached (synthPendingDepth := 1): Out (Wr Nat) (LeafT.T (Wr Nat))
[Meta.synthPending] synthPending ?m.2
[Meta.synthInstance.cache] cached (synthPendingDepth := 2): LeafT (Wr Nat)
-/
#guard_msgs in
run_meta withTCTrace do
  discard <| synthInstance? (mkApp2 (mkConst ``Out) wrNat (projT (← mkFreshExprMVar leafTWr)))
  discard <| atDepth 1 do
    synthInstance? (mkApp2 (mkConst ``Out) wrNat (projT (← mkFreshExprMVar leafTWr)))

/-!
A local instance of type `Root (LeafT.T (Wr Nat) ?hP)` forces `synthPending ?hP` *inside*
the search for the rigid goal `Root Nat`, so the entry is depth-sensitive: the depth-0
entry is reused at depth 0 but not at depth 1.
-/
/--
trace: [Meta.synthInstance.cache] new: Root Nat
[Meta.synthPending] synthPending ?m.1
[Meta.synthInstance.cache] new (synthPendingDepth := 1): LeafT (Wr Nat)
[Meta.synthPending] synthPending ?m.1
[Meta.synthInstance.cache] cached (synthPendingDepth := 1): LeafT (Wr Nat)
[Meta.synthInstance.cache] cached: Root Nat
[Meta.synthInstance.cache] new (synthPendingDepth := 1): Root Nat
-/
#guard_msgs in
run_meta do
  let hP ← mkFreshExprMVar leafTWr
  withLocalDecl `linst .instImplicit (mkApp (mkConst ``Root) (projT hP)) fun _ => withTCTrace do
    discard <| synthInstance? rootNat
    discard <| synthInstance? rootNat
    discard <| atDepth 1 do synthInstance? rootNat

/-!
Issue #2522: at depth 2, `synthPending` gives up (`synthPendingDepth > maxSynthPendingDepth`)
and the query *fails*. Here the failure aborts the search with an `isDefEqStuck` exception,
so nothing is cached at all (both depth-2 queries recompute), and in particular the depth-0
query is unaffected by the depth-2 failures and succeeds.
-/
/--
info: depth 2: failed
---
info: depth 0: synthesized
---
trace: [Meta.synthInstance.cache] new (synthPendingDepth := 2): Root Nat
[Meta.synthPending] too many nested synthPending invocations
[Meta.synthInstance.cache] new (synthPendingDepth := 2): Root Nat
[Meta.synthPending] too many nested synthPending invocations
[Meta.synthInstance.cache] new: Root Nat
[Meta.synthPending] synthPending ?m.1
[Meta.synthInstance.cache] new (synthPendingDepth := 1): LeafT (Wr Nat)
[Meta.synthPending] synthPending ?m.1
[Meta.synthInstance.cache] cached (synthPendingDepth := 1): LeafT (Wr Nat)
-/
#guard_msgs in
run_meta do
  let hP ← mkFreshExprMVar leafTWr
  withLocalDecl `linst .instImplicit (mkApp (mkConst ``Root) (projT hP)) fun _ => withTCTrace do
    let r2 ← atDepth 2 do trySynthInstance rootNat
    let r2' ← atDepth 2 do trySynthInstance rootNat
    logInfo m!"depth 2: {if r2.toOption.isSome || r2'.toOption.isSome then "synthesized" else "failed"}"
    let r0 ← synthInstance? rootNat
    logInfo m!"depth 0: {if r0.isSome then "synthesized" else "failed"}"

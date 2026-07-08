/-!
Repro for why `tryResolve` cannot skip the final `isDefEq mvar instVal` (the "recheck")
when the goal type contains metavariables. Distilled from
`Mathlib/Order/SuccPred/LinearLocallyFinite.lean` (`toZ`).

The key ingredient: `pred_eq` below is a CLASS PROJECTION. Projections demote the
class's own parameters to PLAIN implicit binders:

  @IsPredArch.pred_eq : ∀ {α} {inst : Preorder' α} {inst_1 : PredOrder' α}
                          [self : IsPredArch α] {a : α}, ...

So when `pred_eq (α := ι) (a := i)` is elaborated, `?pre : Preorder' ι` and
`?pd : PredOrder' ι ?pre` are created as ORDINARY unification metavariables (kind
`natural`, never registered as TC goals). Only `[self]` becomes a TC problem, and its
goal is `IsPredArch ι ?pre ?pd` — the mvars are in the goal handed to `synthInstance`.

`?pre`/`?pd` can only ever be assigned by (a) unification, or (b) `synthPending` when
some unification gets STUCK on them. During the search, matching the candidate
`isPredArch_of_linear` pairs the `PredOrder'` slot as ⟨candidate's fresh mvar, ?pd⟩ —
an "easy case" assignment, never stuck, so (b) never fires there. The recheck is the
one unification where the pair becomes ⟨?pd, ?pd⟩ with BOTH sides read-only (inner
mctx depth): not an easy case, postponed, and `isDefEqArgs`' second pass calls
`trySynthPending ?pd` BEFORE the equality check. `synthPendingImp` raw-assigns
`?pd := <local instance>` and `mkAnswer` bakes it into the answer expression.

Skip the recheck and nothing ever gets stuck on `?pd`: the answer stays parametric in
it, elaboration finishes with an unassigned natural mvar, and you get
"don't know how to synthesize implicit argument".

Behavior (toggle in `src/Lean/Meta/SynthInstance.lean`, end of `tryResolve`):
- recheck always (old code) ............................ compiles
- guarded direct assign (tc_directAssign HEAD) ......... compiles (goal has mvars → recheck branch)
- unconditional direct assign .......................... FAILS on this file

Every declaration below is load-bearing (bisected): the projection with `{inst}`
binders, the named argument `(α := ι)` (changes elaboration order so `?self` is
synthesized before `?pre`/`?pd` are known), the `find'` wrapper (keeps the expected
type from fixing `?pd`), and the `Preorder'` derivation instance (makes the
candidate's `Preorder'` slot a real unification, which pins `?pre` but not `?pd`).
-/
set_option warn.sorry false

class Preorder' (α : Type) : Prop where
class LinearOrder' (α : Type) : Prop where

instance instPreorderOfLinearOrder' (α : Type) [LinearOrder' α] : Preorder' α := ⟨⟩

class PredOrder' (α : Type) [Preorder' α] where
  pred : α → α

class IsPredArch (α : Type) [Preorder' α] [PredOrder' α] : Prop where
  pred_eq : ∀ {a : α}, PredOrder'.pred a = a

export IsPredArch (pred_eq)

instance (priority := 100) isPredArch_of_linear (α : Type) [LinearOrder' α]
    [PredOrder' α] : IsPredArch α := ⟨sorry⟩

def find' {p : Prop} (_h : p) : Nat := 0

def toZ' {ι : Type} [LinearOrder' ι] [PredOrder' ι] (i : ι) : Nat :=
  find' (pred_eq (α := ι) (a := i))

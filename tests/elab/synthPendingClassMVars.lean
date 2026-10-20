/-!
Regression test for TC goals whose class-parameter arguments are pending metavariables
(they rely on the `isDefEq` recheck at the end of `SynthInstance.tryResolve`).

`pred_eq` below is a class projection. Projections demote the class's own parameters to
plain implicit binders:

  @IsPredArch.pred_eq : ∀ {α} {inst : Preorder' α} {inst_1 : PredOrder' α}
                          [self : IsPredArch α] {a : α}, ...

So when `pred_eq (α := ι) (a := i)` is elaborated, `?pre : Preorder' ι` and
`?pd : PredOrder' ι ?pre` are created as ordinary unification metavariables (never
registered as TC problems), and the TC goal for `[self]` is `IsPredArch ι ?pre ?pd`.
During the search, matching the candidate `isPredArch_of_linear` pairs the `PredOrder'`
slot as ⟨candidate's fresh mvar, `?pd`⟩ — an assignment that consumes the slot without
determining `?pd`. Nothing else in the elaborator is responsible for `?pd` (the `find'`
wrapper keeps the expected type from fixing it); the recheck's `isDefEqArgs` second pass
runs `trySynthPending` on it. If `tryResolve` assigned directly without the recheck,
elaboration would end with `?pd` unassigned and this file would fail with "don't know how
to synthesize implicit argument".

Distilled from `Mathlib/Order/SuccPred/LinearLocallyFinite.lean` (`toZ`). Every
declaration is load-bearing: the projection (a standalone theorem with `[...]` binders
does not reproduce), the named argument `(α := ι)` (changes elaboration order so `[self]`
is synthesized while `?pre`/`?pd` are unassigned), the `find'` wrapper, and the
`Preorder'` derivation instance (pins `?pre` via unification but not `?pd`).
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

import Lean.Elab.Command

/-!
Tests that reducibility changes invalidate the type class resolution cache within a command by
birth arithmetic: a change whose target was born after a cached entry's query is skipped during
validation (the query cannot have observed it), while a change to a pre-existing declaration
invalidates the entry. See `Lean.Environment.declChangeLog`.
-/

open Lean Meta Elab Command

class R (α : Type) where

instance : R Nat := ⟨⟩

def MyNat := Nat

-- `MyNat` is semireducible, so resolution cannot unfold it and the failure is cached (`new:`
-- then `cached:`). Marking a *freshly created* constant `[reducible]` leaves the entry alive:
-- the constant was born after the entry's watermark, so the change is skipped (`cached:`).
-- Marking pre-existing `MyNat` `[reducible]` invalidates the entry; `MyNat` now unfolds and the
-- query succeeds (`new:` then `cached:`).
/--
trace: [Meta.synthInstance.cache] new: R MyNat
[Meta.synthInstance.cache] cached: R MyNat
[Meta.synthInstance.cache] cached: R MyNat
[Meta.synthInstance.cache] new: R MyNat
[Meta.synthInstance.cache] cached: R MyNat
-/
#guard_msgs in
run_cmd liftTermElabM do
  let ty := mkApp (mkConst ``R) (mkConst ``MyNat)
  let query : TermElabM Unit :=
    withOptions (·.setBool `trace.Meta.synthInstance.cache true) do
      discard <| synthInstance? ty
  query
  query
  addDecl <| .defnDecl {
    name := `freshHelper, levelParams := [], type := mkConst ``Nat,
    value := mkNatLit 1, hints := .abbrev, safety := .safe }
  Attribute.add `freshHelper `reducible .missing
  query
  Attribute.add ``MyNat `reducible .missing
  query
  query

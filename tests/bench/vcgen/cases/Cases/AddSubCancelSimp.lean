import Lean
import Std.Tactic.Do

/-!
Same benchmark as `AddSubCancel` but using equality (`simp`) specs for `get` and `set`
instead of triple specs. Exercises the simp/equality spec rule-construction path.
-/

open Lean Meta Order Std.Internal.Do

namespace AddSubCancelSimp

set_option mvcgen.warning false

/- TODO: Those lemmas actually not used because priorites are not respected for simp lemmas.
  Moreover, if `vcgen` actually used them, it wpould have lead to a bug:
  ```
  Did not know how to decompose weakest precondition for fun s => pure (s, s)
  ```
  in both implementations!
-/
-- @[spec high]
-- theorem Spec.MonadState_get {m : Type u → Type v} [Monad m] {σ : Type u} :
--     (get : StateT σ m σ) = fun s => pure (s, s) := by
--   rfl

-- @[spec high]
-- theorem Spec.MonadStateOf_set {m : Type u → Type v} [Monad m] {σ : Type u} {s : σ} :
--     (set s : StateT σ m PUnit) = fun _ => pure (⟨⟩, s) := by
--   rfl

def step (v : Nat) : StateM Nat Unit := do
  let s ← get
  set (s + v)
  let s ← get
  set (s - v)

def loop (n : Nat) : StateM Nat Unit := do
  match n with
  | 0 => pure ()
  | n+1 => step n; loop n

def Goal (n : Nat) : Prop := ∀ post, ⦃post⦄ loop n ⦃fun _ => post⦄

end AddSubCancelSimp

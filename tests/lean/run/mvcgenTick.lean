module

public import Std.Do.Triple.Basic
import Std.Tactic.Do

open Std.Do

public section

structure TickM.State where
  count : Nat

@[expose] def TickM (α : Type) := StateM TickM.State α

namespace TickM

instance : Monad TickM := inferInstanceAs (Monad (StateM TickM.State))
instance : LawfulMonad TickM := inferInstanceAs (LawfulMonad (StateM TickM.State))

-- Is this what we want?
instance : Std.Do.WP TickM (.arg TickM.State .pure) := inferInstanceAs (Std.Do.WP (StateM TickM.State) _)

def run (m : TickM α) : α := (StateT.run m ⟨0⟩).1
def tick : TickM Unit := modify (m := StateM _) (fun s => ⟨s.count + 1⟩)
def tick' : TickM Unit := fun s => ⟨(), ⟨s.count + 1⟩⟩

def checkBound (n : Nat) : TickM Bool := fun s => ⟨s.count ≤ n, s⟩
def checkBound' (n : Nat) : Assertion (.arg TickM.State .pure) := fun s => ⌜s.count ≤ n⌝
-- Or if `checkBound'` should be defined without importing `Std.Do`:
-- def checkBound'' (n : Nat) : TickM.State → ULift Prop := fun s => ⟨s.count ≤ n⟩
-- example : checkBound' = checkBound'' := rfl

theorem tick'_spec {Q : PostCond Unit (.arg TickM.State .pure)} :
    ⦃fun s => Q.1 () ⟨s.count+1⟩⦄ tick' ⦃Q⦄ := by
  simp [tick', Triple, wp, Id.run]

public theorem checkBound_tick' (n : Nat) :
    ⦃checkBound' n⦄ tick ⦃⇓ _ => checkBound' (n + 1)⦄ := by
  set_option trace.Elab.Tactic.Do.vcgen true in
  -- set_option trace.Debug.Meta.Tactic.simp true in
  set_option trace.Meta.Tactic.simp true in
  set_option trace.Meta.realizeConst true in
  -- set_option trace.Debug.Meta.Tactic.simp.congr true in
  mvcgen [tick]
  -- Even if I remove the `private` modifier on `count`, I only get as far as
  -- case vc1
  -- n : Nat
  -- ⊢ ∀ (s : State),
  --   (checkBound' n s).down →
  --     (wp⟦fun s => ((), { count := s.count + 1 })⟧ (PostCond.noThrow fun x => checkBound' (n + 1)) s).down
  -- Which `mvcgen` should have "eta-expanded".

end TickM
end -- public section

namespace TickM

end TickM

import Concurrent
import Collector

/-!
Bind the production shared release decision to separately observed counter values. The first read,
sticky check, and atomic update can each observe a different count. The atomic result then connects
to the ownership invariant preserved by arbitrary histories in `Concurrent.lean`.
-/

namespace RcConcurrent

private def read : StateM (List Int32 × Int32) Int32 := fun (snapshots, current) =>
  match snapshots with
  | [] => (current, ([], current))
  | first :: rest => (first, (rest, current))

private def write (rc : Int32) : StateM (List Int32 × Int32) Unit :=
  fun (snapshots, _) => ((), (snapshots, rc))

private def fetchAdd : StateM (List Int32 × Int32) Int32 :=
  fun (snapshots, current) => (current, (snapshots, current + 1))

def splitRelease (first checked current : Int32) : Bool × Int32 :=
  let (last, (_, rc)) :=
    (Lean.Runtime.GC.releaseLast read write fetchAdd).run ([first, checked], current)
  (last, rc)

theorem shared_release_refines (first checked current : Int32) (shared : first < 0) :
    splitRelease first checked current =
      if checked == 0 || checked ≤ LEAN_RC_STICKY_DROP then (false, current)
      else (current == -1, current + 1) := by
  have hmany : ¬ first > (1 : Int32) := by bv_decide
  have hone : first ≠ (1 : Int32) := by bv_decide
  have one : Int32.ofUInt32 1 = (1 : Int32) := by decide
  have zero : Int32.ofUInt32 0 = (0 : Int32) := by decide
  have drop : Int32.ofUInt32 0xA0000000 = LEAN_RC_STICKY_DROP := by decide
  have final : Int32.ofUInt32 0xFFFFFFFF = (-1 : Int32) := by decide
  unfold splitRelease Lean.Runtime.GC.releaseLast
  simp only [one, zero, drop, final]
  dsimp [read, write, fetchAdd, Bind.bind, Pure.pure, Functor.map,
    StateT.run, StateT.bind, StateT.pure, StateT.map]
  simp only [hmany, hone, beq_iff_eq, ↓reduceIte]
  dsimp [read, fetchAdd, Bind.bind, Pure.pure, StateT.bind, StateT.pure]
  by_cases hs : checked = 0 ∨ checked ≤ LEAN_RC_STICKY_DROP <;>
    simp [hs, StateT.bind, StateT.pure]
  all_goals rfl

theorem production_last_exclusive {s : State} (h : Safe s) (pending : 0 < s.drops)
    (first checked : Int32) (shared : first < 0)
    (last : (splitRelease first checked (Int32.ofInt s.count)).1 = true) :
    s.references = 1 ∧ s.copies = [] ∧ s.owners = 0 := by
  rw [shared_release_refines _ _ _ shared] at last
  split at last
  · contradiction
  · have he := h.counter_encoding (by simp only [State.references]; omega)
    simp only [beq_iff_eq] at last
    have hc : s.count = -1 := by
      have := congrArg Int32.toInt last
      simp only [he] at this
      exact this
    exact h.last_quiescent pending hc

theorem history_last_exclusive (rc : Int32) (owners : Nat)
    (unshared : isUnshared rc) (tracked : tracks (some rc) (some owners)) {s : State}
    (history : History (initial rc owners) s) (pending : 0 < s.drops)
    (first checked : Int32) (shared : first < 0)
    (last : (splitRelease first checked (Int32.ofInt s.count)).1 = true) :
    s.references = 1 ∧ s.copies = [] ∧ s.owners = 0 :=
  production_last_exclusive (history_preserves history (initial_safe rc owners unshared tracked))
    pending first checked shared last

example : splitRelease (-2) (-1) (-1) = (true, 0) := by decide
example : splitRelease (-2) (-2) (-1) = (true, 0) := by decide
example : splitRelease (-2) (-2) (-3) = (false, -2) := by decide
example : splitRelease (LEAN_RC_STICKY_DROP + 1) (LEAN_RC_STICKY_DROP - 1)
    (LEAN_RC_STICKY_DROP - 1) = (false, LEAN_RC_STICKY_DROP - 1) := by decide

end RcConcurrent

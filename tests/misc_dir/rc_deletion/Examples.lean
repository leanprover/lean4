import Schedule

/-!
Concrete heaps for the ownership specification of deletion.

Fields are occurrences, so repeated pointers still release separate references. Cycles and
never-freed counts keep their objects, and must not release those objects' fields. `Released`
rejects a release that reclaims nothing or parks a surviving object at a sticky count, and leaves an
unreferenced cycle open. The traces show `drain`'s last-in, first-out order, which is not a
contract: a first-in, first-out schedule below ends in an equivalent state. The file ends with the
axioms of the headline theorems.
-/

namespace RcGraph.Examples

private def owners (roots fields : Nat) : Ownership roots fields :=
  (List.finRange roots).map Token.root ++ (List.finRange fields).map Token.field

private def st (n : Nat) : Int32 := Int32.ofNat n
private def mt (n : Nat) : Int32 := -st n

private def initial (g : Graph α objects roots fields) (encode : Nat → Int32) :
    State objects roots fields :=
  { own := owners roots fields
    rc := fun o => some (encode (count g (owners roots fields) o)) }

private def trace (s : State objects roots fields) : List Nat :=
  s.freed.reverse.map Fin.val

private def deleteRoot (g : Graph α objects roots fields) (s : State objects roots fields)
    (r : Fin roots) : State objects roots fields :=
  drain g (drop g s (.root r))

private def repeated : Graph Nat 2 1 3 :=
  { payload := Fin.val, root := fun _ => 0, source := fun _ => 0, target := fun _ => 1 }

example : Valid repeated (initial repeated st) := by unfold Valid; decide
example : Valid repeated (initial repeated mt) := by unfold Valid; decide
example : QueueSafe (initial repeated st) := by unfold QueueSafe; decide

#guard trace (deleteRoot repeated (initial repeated st) 0) == [0, 1]
#guard trace (deleteRoot repeated (initial repeated mt) 0) == [0, 1]
#guard (deleteRoot repeated (initial repeated st) 0).own.isEmpty

private def siblings : Graph Nat 4 1 3 :=
  { payload := Fin.val, root := fun _ => 0, source := fun _ => 0
    target := fun f => ⟨f.val + 1, by omega⟩ }

example : Valid siblings (initial siblings st) := by unfold Valid; decide

-- All fields are released before the last child queued is deleted.
#guard trace (deleteRoot siblings (initial siblings st) 0) == [0, 3, 2, 1]
#guard trace (deleteRoot siblings (initial siblings mt) 0) == [0, 3, 2, 1]

private def diamond : Graph Nat 4 2 4 :=
  { payload := Fin.val, root := fun r => if r == 0 then 0 else 1
    source := fun f => if f < 2 then 0 else if f == 2 then 1 else 2
    target := fun f => if f == 0 then 1 else if f == 1 then 2 else 3 }

example : Valid diamond (initial diamond st) := by unfold Valid; decide
example : Valid diamond (initial diamond mt) := by unfold Valid; decide

private def partialDiamond := deleteRoot diamond (initial diamond st) 0

#guard trace partialDiamond == [0, 2]
#guard partialDiamond.own == [.root 1, .field 2]
#guard observe diamond partialDiamond 1 == some 1
#guard observe diamond partialDiamond 3 == some 3
#guard partialDiamond.rc 3 == some 1
#guard trace (deleteRoot diamond partialDiamond 1) == [0, 2, 1, 3]
#guard trace (deleteRoot diamond (deleteRoot diamond (initial diamond mt) 0) 1) == [0, 2, 1, 3]
#guard (deleteRoot diamond partialDiamond 1).own.isEmpty

private def sharedRoots : Graph Nat 1 2 0 :=
  { payload := Fin.val, root := fun _ => 0, source := Fin.elim0, target := Fin.elim0 }

example : Valid sharedRoots (initial sharedRoots st) := by unfold Valid; decide

#guard (deleteRoot sharedRoots (initial sharedRoots st) 0).freed.isEmpty
#guard trace (deleteRoot sharedRoots (deleteRoot sharedRoots (initial sharedRoots st) 0) 1) == [0]
#guard trace (deleteRoot sharedRoots (deleteRoot sharedRoots (initial sharedRoots mt) 0) 1) == [0]

private def cycle : Graph Nat 2 1 2 :=
  { payload := Fin.val, root := fun _ => 0, source := id
    target := fun f => if f == 0 then 1 else 0 }

example : Valid cycle (initial cycle st) := by unfold Valid; decide
example : Valid cycle (initial cycle mt) := by unfold Valid; decide

-- A cycle keeps its objects, with their counts and fields.
#guard (deleteRoot cycle (initial cycle st) 0).freed.isEmpty
#guard (deleteRoot cycle (initial cycle st) 0).own.length == 2
#guard (deleteRoot cycle (initial cycle st) 0).rc 0 == some 1
#guard (deleteRoot cycle (initial cycle mt) 0).rc 0 == some (-1)

private def chain : Graph Nat 3 1 2 :=
  { payload := Fin.val, root := fun _ => 0
    source := fun f => ⟨f.val, by omega⟩
    target := fun f => ⟨f.val + 1, by omega⟩ }

private def retained (rc : Int32) : State 3 1 2 :=
  { initial chain st with rc := set (initial chain st).rc 0 (some rc) }

example : Valid chain (retained 0) := by unfold Valid; decide
example : Valid chain (retained LEAN_RC_STICKY) := by unfold Valid; decide
example : Valid chain (retained LEAN_RC_STICKY_DROP) := by unfold Valid; decide
example : Valid chain (retained Int32.minValue) := by unfold Valid; decide

-- A persistent or sticky parent keeps its fields, and so its descendants.
#guard [0, LEAN_RC_STICKY, LEAN_RC_STICKY_DROP, Int32.minValue].all fun rc =>
  let s := deleteRoot chain (retained rc) 0
  s.freed.isEmpty && s.todo.isEmpty && s.own.length == 2 &&
    s.rc 0 == some rc && observe chain s 1 == some 1 && observe chain s 2 == some 2

-- Just above the drop threshold a shared count is still released.
#guard (deleteRoot chain (retained (LEAN_RC_STICKY_DROP + 1)) 0).rc 0 ==
  some (LEAN_RC_STICKY_DROP + 2)

/-! ## `Released` -/

private theorem diamond_quiescent : Quiescent diamond (initial diamond st) :=
  ⟨by unfold Valid; decide, by unfold QueueSafe; decide, rfl, by decide⟩

private theorem diamond_released : Released diamond (initial diamond st) 0 partialDiamond :=
  (drain_released diamond_quiescent 0).1

example : Complete diamond partialDiamond ∧ partialDiamond.todo = [] ∧ partialDiamond.freed.Nodup :=
  ⟨diamond_released.complete, diamond_released.todo, diamond_released.nodup⟩

-- The other root still reaches the shared object through a field that was never released.
example : observe diamond partialDiamond 3 = some 3 := by
  have hp : Reachable diamond 1 3 := .field 2 .root
  calc
    observe diamond partialDiamond 3 = observe diamond (initial diamond st) 3 :=
      diamond_released.observations 1 (by decide) (by decide) 3 hp
    _ = some 3 := by decide

-- Object 1 lost one of its two references, and its counter took one `decRef`.
#guard partialDiamond.rc 1 == decRefs 1 (some 2) &&
  count diamond (initial diamond st).own 1 - count diamond partialDiamond.own 1 == 1

/-- A release that reclaims nothing and parks the root's object at a sticky count. -/
private def parked : State 3 1 2 :=
  { own := [.field 0, .field 1], rc := fun o => if o = 0 then some LEAN_RC_STICKY else some 1 }

private def chainState : State 3 1 2 :=
  { own := [.root 0, .field 0, .field 1], rc := fun _ => some 1 }

-- Every clause but `counters` holds: the counts track the remaining references, nothing is
-- queued, nothing was reclaimed and no object lost its count, the released token is the root's,
-- and there is no other root.
example : Valid chain parked ∧ parked.todo = [] ∧ QueueSafe parked ∧
    (∀ o, o ∈ parked.freed ↔
      o ∈ chainState.freed ∨ ((chainState.rc o).isSome ∧ parked.rc o = none)) ∧
    (∀ t, t ∈ parked.own ↔ t ∈ chainState.own ∧ t ≠ .root 0 ∧
      ∀ f, t = .field f → chain.source f ∉ parked.freed) ∧
    (∀ r : Fin 1, r ≠ 0 → False) := by
  refine ⟨by unfold Valid; decide, rfl, by unfold QueueSafe; decide, by decide, ?_,
    fun r hne => hne (Fin.fin_one_eq_zero r)⟩
  intro t
  cases t with
  | root r => simp [parked, chainState, Fin.fin_one_eq_zero r]
  | field f => simp [parked, chainState]

example : ¬ Released chain chainState 0 parked := fun h => by
  have := h.counters 0
  revert this; decide

#guard trace (deleteRoot chain chainState 0) == [0, 1, 2]

/-- A release that parks a surviving object at a sticky count, so a later release leaks it. -/
private def stuck : State 1 2 0 := { own := [.root 1], rc := fun _ => some LEAN_RC_STICKY }

example : Valid sharedRoots stuck := by unfold Valid; decide

example : ¬ Released sharedRoots (initial sharedRoots st) 0 stuck := fun h => by
  have := h.counters 0
  revert this; decide

/--
`Released` does not decide an unreferenced cycle. Releasing the root of `cycle` leaves its two
objects referencing each other; reclaiming both also meets every clause, though no schedule of
`Step` does it. `drain_released` rules it out by its second conjunct.
-/
private def cycleReclaimed : State 2 1 2 := { own := [], rc := fun _ => none, freed := [1, 0] }

example : Released cycle (initial cycle st) 0 cycleReclaimed where
  valid := by unfold Valid; decide
  todo := rfl
  queueSafe := by unfold QueueSafe; decide
  freed := by decide
  own := by
    intro t
    cases t with
    | root r => simp [cycleReclaimed, initial, owners, Fin.fin_one_eq_zero r]
    | field f => simp [cycleReclaimed, initial, owners, cycle]; revert f; decide
  counters := by decide
  observations := fun r hne => absurd (Fin.fin_one_eq_zero r) hne

/-! ## Another schedule -/

/-- Deleting the children of `siblings` first in, first out. -/
private def fifo : State 4 1 3 :=
  let s := drop siblings (initial siblings st) (.root 0)
  let s := drop siblings s (.field 0)
  let s := drop siblings s (.field 1)
  let s := drop siblings s (.field 2)
  let s := reclaimAt s 0
  let s := reclaimAt s 1
  let s := reclaimAt s 2
  reclaimAt s 3

private theorem fifo_steps :
    Steps siblings (drop siblings (initial siblings st) (.root 0)) fifo := by
  refine .step (.release (f := 0) (by decide) (by decide)) ?_
  refine .step (.release (f := 1) (by decide) (by decide)) ?_
  refine .step (.release (f := 2) (by decide) (by decide)) ?_
  refine .step (.reclaim (o := 0) (by decide) (by decide)) ?_
  refine .step (.reclaim (o := 1) (by decide) (by decide)) ?_
  refine .step (.reclaim (o := 2) (by decide) (by decide)) ?_
  exact .step (.reclaim (o := 3) (by decide) (by decide)) (.refl _)

private theorem fifo_stuck : Stuck siblings fifo := by
  have hown : fifo.own = [] := by decide
  have htodo : fifo.todo = [] := by decide
  intro s' h
  cases h with
  | release hf _ => simp [hown] at hf
  | reclaim ho _ => simp [htodo] at ho

#guard trace fifo == [0, 1, 2, 3]

-- `drain`'s order differs, and ends in an equivalent state.
example : Equiv fifo (deleteRoot siblings (initial siblings st) 0) :=
  (drain_released ⟨by unfold Valid; decide, by unfold QueueSafe; decide, rfl, by decide⟩ 0).2 _
    fifo_steps fifo_stuck

/-! ## Axioms -/

/-- info: 'decCascade_eq_decRef' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms decCascade_eq_decRef

/-- info: 'decCascade_never_freed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms decCascade_never_freed

/--
info: 'RcGraph.schedule_independent' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms schedule_independent

/-- info: 'RcGraph.drain_released' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms drain_released

/--
info: 'RcGraph.Released.garbage_freed' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Released.garbage_freed

end RcGraph.Examples

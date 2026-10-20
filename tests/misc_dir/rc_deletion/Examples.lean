import Refinement

/-!
Concrete heaps for the ownership specification of deletion, and for the cascade that implements it.

Fields are occurrences, so repeated pointers still release separate references. Cycles and
never-freed counts keep their objects, and must not release those objects' fields. `Released`
rejects a release that reclaims nothing or parks a surviving object at a sticky count, and leaves an
unreferenced cycle open. The traces show `drain`'s last-in, first-out order, which is not a
contract: a first-in, first-out schedule below ends in an equivalent state. The cascade runs on
layouts that mix immediates, thunk and `Ref` members that are `NULL`, and kinds without members;
invalid layouts are rejected by `Layout.Valid`, and the heap records a fault. The file ends with
the axioms of the headline theorems.
-/

namespace RcGraph.Examples

open Lean.Runtime.Deletion

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

/-! ## The cascade on the runtime's layouts -/

/-- Every object a constructor whose slots are its fields. -/
private def layout (g : Graph α objects roots fields) : Layout objects fields :=
  { tag := fun _ => 0, members := fun o => (g.children o).map .field }

private theorem lt_size {n : Nat} (h : n < 4294967296) : n < USize.size := by
  cases USize.size_eq <;> omega

private theorem layout_valid (g : Graph α objects roots fields) (h : fields < 4294967296) :
    (layout g).Valid g := by
  intro o
  refine ⟨?_, ?_, ?_⟩
  · simp [layout, List.filterMap_map, Function.comp_def, Member.field?]
  · simp [layout, shapeOk, hasSlots]
  · simp only [layout, List.length_map]
    have := List.length_filter_le (fun f => g.source f == o) (List.finRange fields)
    exact lt_size (by simp only [Graph.children, List.length_finRange] at this ⊢; omega)

/-- Whether releasing root `r` broke the access protocol. -/
private def faults (g : Graph α objects roots fields) (l : Layout objects fields)
    (s : State objects roots fields) (r : Fin roots) : Bool :=
  (decRoot g l s r).fault

-- The cascade deletes in `drain`'s order, and keeps the protocol.
#guard trace (collect repeated (layout repeated) (initial repeated st) 0) == [0, 1]
#guard trace (collect siblings (layout siblings) (initial siblings mt) 0) == [0, 3, 2, 1]
#guard trace (collect diamond (layout diamond)
  (collect diamond (layout diamond) (initial diamond st) 0) 1) == [0, 2, 1, 3]
#guard !faults siblings (layout siblings) (initial siblings mt) 0
#guard (collect cycle (layout cycle) (initial cycle st) 0).freed.isEmpty
#guard [0, LEAN_RC_STICKY, LEAN_RC_STICKY_DROP, Int32.minValue].all fun rc =>
  let s := collect chain (layout chain) (retained rc) 0
  s.freed.isEmpty && s.own.length == 2 && s.rc 0 == some rc

private def withLayout (g : Graph α objects roots fields) (o : Fin objects) (tag : UInt8)
    (ms : List (Member fields)) : Layout objects fields :=
  { tag := fun p => if p = o then tag else (layout g).tag p
    members := fun p => if p = o then ms else (layout g).members p }

private theorem withLayout_valid (g : Graph α objects roots fields) (o : Fin objects)
    (tag : UInt8) (ms : List (Member fields)) (h : fields < 4294967296)
    (hf : ms.filterMap Member.field? = g.children o) (hs : shapeOk tag ms = true)
    (hn : ms.length < 4294967296) : (withLayout g o tag ms).Valid g := by
  intro p
  by_cases hp : p = o
  · subst hp; simp [withLayout, hf, hs, lt_size hn]
  · simpa [withLayout, hp] using layout_valid g h p

private def thunkPair : Graph Nat 3 1 2 :=
  { payload := Fin.val, root := fun _ => 0, source := fun _ => 0
    target := fun f => ⟨f.val + 1, by omega⟩ }

private def pairLayout := withLayout thunkPair 0 LeanThunk [.field 0, .field 1]

example : pairLayout.Valid thunkPair :=
  withLayout_valid _ _ _ _ (by decide) (by decide) (by decide) (by decide)
example : Valid thunkPair (initial thunkPair st) := by unfold Valid; decide

-- Both members hold references; the value is released after the closure.
#guard trace (collect thunkPair pairLayout (initial thunkPair st) 0) == [0, 2, 1]
#guard trace (collect thunkPair pairLayout (initial thunkPair mt) 0) == [0, 2, 1]
#guard (collect thunkPair pairLayout (initial thunkPair st) 0).own.isEmpty
#guard !faults thunkPair pairLayout (initial thunkPair st) 0

private def thunkSingle : Graph Nat 2 1 1 :=
  { payload := Fin.val, root := fun _ => 0, source := fun _ => 0, target := fun _ => 1 }

private def unevaluated := withLayout thunkSingle 0 LeanThunk [.field 0, .null]
private def evaluated := withLayout thunkSingle 0 LeanThunk [.null, .field 0]
private def refLayout := withLayout thunkSingle 0 LeanRef [.field 0]

example : unevaluated.Valid thunkSingle :=
  withLayout_valid _ _ _ _ (by decide) (by decide) (by decide) (by decide)
example : evaluated.Valid thunkSingle :=
  withLayout_valid _ _ _ _ (by decide) (by decide) (by decide) (by decide)
example : refLayout.Valid thunkSingle :=
  withLayout_valid _ _ _ _ (by decide) (by decide) (by decide) (by decide)

#guard trace (collect thunkSingle unevaluated (initial thunkSingle st) 0) == [0, 1]
#guard trace (collect thunkSingle evaluated (initial thunkSingle mt) 0) == [0, 1]
#guard trace (collect thunkSingle refLayout (initial thunkSingle st) 0) == [0, 1]
#guard [unevaluated, evaluated, refLayout].all fun l =>
  !faults thunkSingle l (initial thunkSingle st) 0

private def leaf : Graph Nat 1 1 0 :=
  { payload := Fin.val, root := fun _ => 0, source := Fin.elim0, target := Fin.elim0 }

-- `lean_st_ref_take` leaves a `Ref` without a value, and a thunk can have neither member.
private def emptyRef := withLayout leaf 0 LeanRef [.null]
private def emptyThunk := withLayout leaf 0 LeanThunk [.null, .null]

example : emptyRef.Valid leaf :=
  withLayout_valid _ _ _ _ (by decide) (by decide) (by decide) (by decide)
example : emptyThunk.Valid leaf :=
  withLayout_valid _ _ _ _ (by decide) (by decide) (by decide) (by decide)

#guard [emptyRef, emptyThunk].all fun l =>
  trace (collect leaf l (initial leaf st) 0) == [0] && !faults leaf l (initial leaf st) 0

-- Every kind without members is reclaimed by its own terminal effect.
#guard [LeanPromise, LeanScalarArray, LeanString, LeanMPZ, LeanTask, LeanExternal].all fun t =>
  let l := withLayout leaf 0 t []
  trace (collect leaf l (initial leaf st) 0) == [0] && !faults leaf l (initial leaf st) 0

-- Immediates in constructor, closure and array slots hold no references.
#guard [0, LeanMaxCtorTag, LeanClosure, LeanArray].all fun t =>
  let l := withLayout leaf 0 t [.scalar, .scalar, .scalar]
  trace (collect leaf l (initial leaf mt) 0) == [0] && !faults leaf l (initial leaf mt) 0

private def mixedLayout := withLayout siblings 0 LeanArray
  [.scalar, .field 0, .scalar, .field 1, .field 2, .scalar]

example : mixedLayout.Valid siblings :=
  withLayout_valid _ _ _ _ (by decide) (by decide) (by decide) (by decide)

#guard trace (collect siblings mixedLayout (initial siblings st) 0) == [0, 3, 2, 1]
#guard (collect siblings mixedLayout (initial siblings st) 0).own.isEmpty

private def repeatedSlots := withLayout repeated 0 LeanClosure
  [.scalar, .field 0, .scalar, .field 1, .field 2, .scalar]

private theorem repeatedSlots_valid : repeatedSlots.Valid repeated :=
  withLayout_valid _ _ _ _ (by decide) (by decide) (by decide) (by decide)

#guard trace (collect repeated repeatedSlots (initial repeated st) 0) == [0, 1]
#guard trace (collect repeated repeatedSlots (initial repeated mt) 0) == [0, 1]

example : (collect repeated repeatedSlots (initial repeated st) 0).freed.Nodup :=
  (collect_released _ repeatedSlots_valid
    ⟨by unfold Valid; decide, by unfold QueueSafe; decide, rfl, by decide⟩ 0).1.nodup

/-! ## Invalid layouts -/

/-- `NULL` in a constructor slot, which the cascade would release as a pointer. -/
private def nullSlot := withLayout repeated 0 0 [.field 0, .null, .field 1, .field 2]

example : ¬ nullSlot.Valid repeated := fun h => absurd (h 0).2.1 (by decide)
#guard faults repeated nullSlot (initial repeated st) 0

/-- A thunk with a third member, which the cascade never reads. -/
private def wideThunk := withLayout repeated 0 LeanThunk [.field 0, .field 1, .field 2]

example : ¬ wideThunk.Valid repeated := fun h => absurd (h 0).2.1 (by decide)
#guard (collect repeated wideThunk (initial repeated st) 0).own.length == 1

/-- `LeanStructArray` and `LeanReserved`, which no runtime object has. -/
example : ¬ (withLayout leaf 0 LeanStructArray []).Valid leaf := fun h =>
  absurd (h 0).2.1 (by decide)
#guard [LeanStructArray, LeanReserved].all fun t =>
  let l := withLayout leaf 0 t []
  faults leaf l (initial leaf st) 0 && (collect leaf l (initial leaf st) 0).freed.isEmpty

/-- Slots in another order than the field occurrences, or one occurrence twice. -/
example : ¬ (withLayout siblings 0 0 [.field 2, .field 1, .field 0]).Valid siblings := fun h => by
  have := (h 0).1; revert this; decide
example : ¬ (withLayout repeated 0 0 [.field 0, .field 0, .field 2]).Valid repeated := fun h => by
  have := (h 0).1; revert this; decide

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

/-- info: 'RcGraph.collect_released' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms collect_released

/-- info: 'RcGraph.collect_safe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms collect_safe

end RcGraph.Examples

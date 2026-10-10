import Refinement

/-!
Executable ownership graphs exercise the production Lean entry point, queue, thunk dispatch, and loop.
Fields are occurrences, so repeated pointers still consume separate references. Cycles and
never-freed counts deliberately retain objects; they must not release the retained objects' fields.
Physical slot regressions include ignored values, exact counts, and retained-root observations.
-/

namespace RcGraph.Examples

private def owners (roots fields : Nat) : Ownership roots fields :=
  (List.finRange roots).map Token.root ++ (List.finRange fields).map Token.field

private def st (n : Nat) : Int32 := Int32.ofUInt32 (UInt32.ofNat n)
private def mt (n : Nat) : Int32 := -st n

private def initial (g : Graph α objects roots fields) (encode : Nat → Int32) :
    State objects roots fields :=
  { own := owners roots fields
    rc := fun o => some (encode (count g (owners roots fields) o)) }

private def layout (g : Graph α objects roots fields) : Layout objects fields :=
  { slots := fun o => (g.children o).map some
    count := fun o => USize.ofNat (g.children o).length }

private theorem layout_valid (g : Graph α objects roots fields)
    (h : ∀ o, (g.children o).length < 4294967296) : (layout g).Valid g := by
  refine ⟨?_, by simp [layout], by simp [layout]⟩
  intro o
  simpa only [layout, List.length_map] using USize.toNat_ofNat_of_lt_32 (h o)

private def deleteRoot (g : Graph α objects roots fields) (s : State objects roots fields)
    (r : Fin roots) : State objects roots fields :=
  collect g (layout g) s r

private def trace (s : State objects roots fields) : List Nat :=
  s.freed.reverse.map Fin.val

private def repeated : Graph Nat 2 1 3 :=
  { payload := Fin.val, root := fun _ => 0, source := fun _ => 0, target := fun _ => 1 }

example : Valid repeated (initial repeated st) := by unfold Valid; decide
example : Valid repeated (initial repeated mt) := by unfold Valid; decide
example : QueueSafe (initial repeated st) := by unfold QueueSafe; decide

#guard trace (deleteRoot repeated (initial repeated st) 0) == [0, 1]
#guard trace (deleteRoot repeated (initial repeated mt) 0) == [0, 1]
#guard (deleteRoot repeated (initial repeated st) 0).own.isEmpty
#guard (deleteRoot repeated (initial repeated st) 0).todo.isEmpty

private def siblings : Graph Nat 4 1 3 :=
  { payload := Fin.val, root := fun _ => 0, source := fun _ => 0
    target := fun f => ⟨f.val + 1, by omega⟩ }

example : Valid siblings (initial siblings st) := by unfold Valid; decide

-- All fields are released before visiting the last newly dead child.
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
#guard observe diamond partialDiamond 1 == some 1
#guard observe diamond partialDiamond 3 == some 3
#guard partialDiamond.rc 3 == some 1
#guard trace (deleteRoot diamond partialDiamond 1) == [0, 2, 1, 3]
#guard trace (deleteRoot diamond (deleteRoot diamond (initial diamond mt) 0) 1) ==
  [0, 2, 1, 3]
#guard (deleteRoot diamond partialDiamond 1).own.isEmpty

private def sharedRoots : Graph Nat 1 2 0 :=
  { payload := Fin.val, root := fun _ => 0, source := Fin.elim0, target := Fin.elim0 }

example : Valid sharedRoots (initial sharedRoots st) := by unfold Valid; decide

#guard (deleteRoot sharedRoots (initial sharedRoots st) 0).freed.isEmpty
#guard trace (deleteRoot sharedRoots (deleteRoot sharedRoots (initial sharedRoots st) 0) 1) ==
  [0]

private def cycle : Graph Nat 2 1 2 :=
  { payload := Fin.val, root := fun _ => 0, source := id
    target := fun f => if f == 0 then 1 else 0 }

example : Valid cycle (initial cycle st) := by unfold Valid; decide
example : Valid cycle (initial cycle mt) := by unfold Valid; decide

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

-- Keeping a sticky/persistent parent also keeps its outgoing ownership and descendants.
#guard [0, LEAN_RC_STICKY, LEAN_RC_STICKY_DROP, Int32.minValue].all fun rc =>
  let s := deleteRoot chain (retained rc) 0
  s.freed.isEmpty && s.todo.isEmpty && s.own.length == 2 &&
    s.rc 0 == some rc && observe chain s 1 == some 1 && observe chain s 2 == some 2

private def thunkLayout (g : Graph α objects roots fields) (o : Fin objects)
    (closure value : Option (Fin fields)) : Layout objects fields :=
  { layout g with
    tag := fun p => if p == o then 251 else 0
    slots := fun p => if p == o then [] else (layout g).slots p
    count := fun p => if p == o then 0 else (layout g).count p
    closure := fun p => if p == o then closure else none
    value := fun p => if p == o then value else none }

private theorem thunkLayout_valid (g : Graph α objects roots fields) (o : Fin objects)
    (closure value : Option (Fin fields))
    (h : ∀ p, (g.children p).length < 4294967296)
    (hf : closure.toList ++ value.toList = g.children o) :
    (thunkLayout g o closure value).Valid g := by
  refine ⟨?_, ?_, ?_⟩
  · intro p
    by_cases hp : p = o
    · simp [thunkLayout, hp]
    · simpa [thunkLayout, hp] using (layout_valid g h).1 p
  · intro p ht
    have hp : p ≠ o := by
      intro hp
      simp [thunkLayout, hp] at ht
    simpa [thunkLayout, hp] using (layout_valid g h).2.1 p (by simp [layout])
  · intro p ht
    have hp : p = o := by simpa [thunkLayout] using ht
    simpa [thunkLayout, hp] using hf

private def thunkPair : Graph Nat 3 1 2 :=
  { payload := Fin.val, root := fun _ => 0, source := fun _ => 0
    target := fun f => ⟨f.val + 1, by omega⟩ }

private def pairLayout := thunkLayout thunkPair 0 (some 0) (some 1)

example : pairLayout.Valid thunkPair := thunkLayout_valid _ _ _ _ (by decide) (by decide)
example : Valid thunkPair (initial thunkPair st) := by unfold Valid; decide

-- Both slots own references. Reversing their reads reverses the child reclamation order.
#guard trace (collect thunkPair pairLayout (initial thunkPair st) 0) == [0, 2, 1]
#guard trace (collect thunkPair pairLayout (initial thunkPair mt) 0) == [0, 2, 1]
#guard (collect thunkPair pairLayout (initial thunkPair st) 0).own.isEmpty

private def thunkSingle : Graph Nat 2 1 1 :=
  { payload := Fin.val, root := fun _ => 0, source := fun _ => 0, target := fun _ => 1 }

private def unevaluated := thunkLayout thunkSingle 0 (some 0) none
private def evaluated := thunkLayout thunkSingle 0 none (some 0)

example : unevaluated.Valid thunkSingle := thunkLayout_valid _ _ _ _ (by decide) (by decide)
example : evaluated.Valid thunkSingle := thunkLayout_valid _ _ _ _ (by decide) (by decide)

#guard trace (collect thunkSingle unevaluated (initial thunkSingle st) 0) == [0, 1]
#guard trace (collect thunkSingle evaluated (initial thunkSingle mt) 0) == [0, 1]

private def leaf : Graph Nat 1 1 0 :=
  { payload := Fin.val, root := fun _ => 0, source := Fin.elim0, target := Fin.elim0 }

private def emptyThunkLayout := thunkLayout leaf 0 none none

example : emptyThunkLayout.Valid leaf := thunkLayout_valid _ _ _ _ (by decide) (by decide)

#guard trace (collect leaf emptyThunkLayout (initial leaf st) 0) == [0]

private def arrayLayout (slots : Fin objects → List (Option (Fin fields))) :
    Layout objects fields :=
  { tag := fun _ => 246, slots, count := fun o => USize.ofNat (slots o).length }

private theorem arrayLayout_valid (g : Graph α objects roots fields)
    (slots : Fin objects → List (Option (Fin fields)))
    (h : ∀ o, (slots o).length < 4294967296)
    (hf : ∀ o, (slots o).filterMap id = g.children o) :
    (arrayLayout slots).Valid g :=
  ⟨fun o => USize.toNat_ofNat_of_lt_32 (h o), fun o _ => hf o, by simp [arrayLayout]⟩

private def immediateArrayLayout : Layout 1 0 :=
  arrayLayout fun _ => [none, none, none]

private theorem immediateArray_valid : immediateArrayLayout.Valid leaf :=
  arrayLayout_valid _ _ (by decide) (by decide)

-- Three physical slots own no heap references.
example : (immediateArrayLayout.count 0).toNat = 3 :=
  USize.toNat_ofNat_of_lt_32 (by decide)

#guard trace (collect leaf immediateArrayLayout (initial leaf st) 0) == [0]
#guard trace (collect leaf immediateArrayLayout (initial leaf mt) 0) == [0]
#guard (collect leaf immediateArrayLayout (initial leaf st) 0).own.isEmpty

private theorem leaf_quiescent : Quiescent leaf (initial leaf st) :=
  ⟨by unfold Valid; decide, by unfold QueueSafe; decide, rfl, by decide⟩

example :
    Valid leaf (collect leaf immediateArrayLayout (initial leaf st) 0) ∧
      QueueSafe (collect leaf immediateArrayLayout (initial leaf st) 0) :=
  let h := (collect_released _ immediateArray_valid leaf_quiescent 0).1
  ⟨h.valid, h.queueSafe⟩

private def emptyArrayLayout : Layout 1 0 := arrayLayout fun _ => []

example : emptyArrayLayout.Valid leaf := arrayLayout_valid _ _ (by decide) (by decide)

#guard trace (collect leaf emptyArrayLayout (initial leaf st) 0) == [0]

private def mixedLayout : Layout 4 3 :=
  arrayLayout fun o => if o == 0 then [none, some 0, none, some 1, some 2, none] else []

example : mixedLayout.Valid siblings :=
  arrayLayout_valid _ _ (by decide) (by decide)

#guard trace (collect siblings mixedLayout (initial siblings st) 0) == [0, 3, 2, 1]
#guard trace (collect siblings mixedLayout (initial siblings mt) 0) == [0, 3, 2, 1]
#guard (collect siblings mixedLayout (initial siblings st) 0).own.isEmpty

private def repeatedSlotLayout : Layout 2 3 :=
  arrayLayout fun o => if o == 0 then [none, some 0, none, some 1, some 2, none] else []

private theorem repeatedSlotLayout_valid : repeatedSlotLayout.Valid repeated :=
  arrayLayout_valid _ _ (by decide) (by decide)

#guard trace (collect repeated repeatedSlotLayout (initial repeated st) 0) == [0, 1]
#guard trace (collect repeated repeatedSlotLayout (initial repeated mt) 0) == [0, 1]
#guard (collect repeated repeatedSlotLayout (initial repeated st) 0).own.isEmpty

example : (collect repeated repeatedSlotLayout (initial repeated st) 0).freed.Nodup :=
  (collect_released _ repeatedSlotLayout_valid
    ⟨by unfold Valid; decide, by unfold QueueSafe; decide, rfl, by decide⟩ 0).1.nodup

private def physicalDiamondLayout : Layout 4 4 :=
  arrayLayout fun o =>
    if o == 0 then [none, some 0, none, some 1, none]
    else if o == 1 then [none, some 2, none]
    else if o == 2 then [none, some 3, none]
    else [none, none]

private theorem physicalDiamond_valid : physicalDiamondLayout.Valid diamond :=
  arrayLayout_valid _ _ (by decide) (by decide)

private def physicalDiamond := collect diamond physicalDiamondLayout (initial diamond st) 0

#guard trace physicalDiamond == [0, 2]
#guard physicalDiamond.own == [.root 1, .field 2]
#guard trace (collect diamond physicalDiamondLayout physicalDiamond 1) == [0, 2, 1, 3]

private theorem diamond_released : Released diamond (initial diamond st) 0 physicalDiamond :=
  (collect_released _ physicalDiamond_valid
    ⟨by unfold Valid; decide, by unfold QueueSafe; decide, rfl, by decide⟩ 0).1

example : Valid diamond physicalDiamond ∧ QueueSafe physicalDiamond :=
  ⟨diamond_released.valid, diamond_released.queueSafe⟩

example : Complete diamond physicalDiamond ∧ physicalDiamond.todo = [] :=
  ⟨diamond_released.complete, diamond_released.todo⟩

example : physicalDiamond.freed.Nodup := diamond_released.nodup

-- The retained root still reaches the shared descendant through its unscanned field.
example : observe diamond physicalDiamond 3 = some 3 := by
  have hp : Reachable diamond 1 3 := .field 2 .root
  calc
    observe diamond physicalDiamond 3 = observe diamond (initial diamond st) 3 :=
      diamond_released.observations 1 (by decide) (by decide) 3 hp
    _ = some 3 := by decide

private def undercountedLayout : Layout 4 3 :=
  { mixedLayout with count := (layout siblings).count }

-- Counting only present references misses later fields and fails the layout contract.
example : ¬ undercountedLayout.Valid siblings := by
  intro hl
  have hn := hl.1 0
  change (3 : USize).toNat = 6 at hn
  have h3 : (3 : USize).toNat = 3 := USize.toNat_ofNat_of_lt_32 (by decide)
  omega

#guard trace (collect siblings undercountedLayout (initial siblings st) 0) == [0, 1]
#guard (collect siblings undercountedLayout (initial siblings st) 0).own.length == 2

private def duplicateSlotLayout : Layout 2 3 :=
  arrayLayout fun o => if o == 0 then [none, some 0, none, some 0, some 2, none] else []

-- Equal target pointers do not permit substituting one ownership occurrence for another.
example : ¬ duplicateSlotLayout.Valid repeated := by
  intro hl
  have hf : (duplicateSlotLayout.slots 0).filterMap id ≠ repeated.children 0 := by decide
  exact hf (hl.2.1 0 (by decide))

private def reversedSlotLayout : Layout 4 3 :=
  arrayLayout fun o => if o == 0 then [none, some 2, none, some 1, some 0, none] else []

example : ¬ reversedSlotLayout.Valid siblings := by
  intro hl
  have hf : (reversedSlotLayout.slots 0).filterMap id ≠ siblings.children 0 := by decide
  exact hf (hl.2.1 0 (by decide))

private def oversizedLayout : Layout 1 0 :=
  { tag := fun _ => 246, slots := fun _ => List.replicate USize.size none
    count := fun _ => USize.ofNat USize.size }

-- The bound is symbolic: no enormous list is evaluated to establish wraparound rejection.
example : ¬ oversizedLayout.Valid leaf := by
  intro hl
  have hn := hl.slots_length_lt 0
  simp only [oversizedLayout, List.length_replicate, Nat.lt_irrefl] at hn

private def emptyGraph : Graph Nat 0 0 0 :=
  { payload := Fin.elim0, root := Fin.elim0, source := Fin.elim0, target := Fin.elim0 }

#guard (drain emptyGraph { own := [], rc := Fin.elim0 }).freed.isEmpty

end RcGraph.Examples

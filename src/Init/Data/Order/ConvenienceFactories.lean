module

prelude
public import Init.Data.Order.FactoriesExtra
public import Init.Data.Order.LemmasExtra

namespace Std

section LinearPreorder

namespace FactoryInstances

public scoped instance instLEOfOrd {α : Type u} [Ord α] :
    LE α where
  le a b := (compare a b).isLE

public instance instLawfulOrderOrdOfOrd {α : Type u} [Ord α] [OrientedOrd α] :
    LawfulOrderOrd α where
  compare_isLE a b := by simp [LE.le]
  compare_isGE a b := by simp [OrientedCmp.isGE_iff_isLE, LE.le]

public scoped instance instDecidableLEOfOrd {α : Type u} [LE α] [Ord α] [LawfulOrderOrd α] :
    DecidableLE α :=
  fun a b => match h : (compare a b).isLE with
    | true => isTrue (by simpa only [LawfulOrderOrd.compare_isLE] using h)
    | false => isFalse (by simpa only [LawfulOrderOrd.compare_isLE_eq_false] using h)

public theorem _root_.Std.OrientedCmp.of_gt_iff_lt {α : Type u} {cmp : α → α → Ordering}
    (h : ∀ a b : α, cmp a b = .gt ↔ cmp b a = .lt) : OrientedCmp cmp where
  eq_swap {a b} := by
    cases h' : cmp a b
    · apply Eq.symm
      simp [h, h']
    · cases h'' : cmp b a
      · simp [← h, h'] at h''
      · simp
      · simp [h, h'] at h''
    · apply Eq.symm
      simp [← h, h']

public scoped instance instLTOfOrd {α : Type u} [Ord α] :
    LT α where
  lt a b := compare a b = .lt

public instance instLawfulOrderLTOfOrd {α : Type u} [Ord α] [LE α] [LawfulOrderOrd α] :
    LawfulOrderLT α where
  lt_iff {a b} := by
    simp +contextual [LT.lt, ← Std.compare_isLE (a := a), ← Std.compare_isGE (a := a)]

public scoped instance instDecidableLTOfOrd {α : Type u} [LT α] [Ord α] [LawfulOrderOrd α]
    [LawfulOrderLT α] :
    DecidableLT α :=
  fun a b => if h : compare a b = .lt then
      isTrue (by simpa only [compare_eq_lt] using h)
    else
      isFalse (by simpa only [compare_eq_lt] using h)

public scoped instance instBEqOfOrd {α : Type u} [Ord α] :
    BEq α where
  beq a b := compare a b = .eq

public instance instLawfulOrderBEqOfOrd {α : Type u} [Ord α] [LE α] [LawfulOrderOrd α] :
    LawfulOrderBEq α where
  beq_iff_le_and_ge {a b} := by
    simp +contextual [BEq.beq, ← Std.compare_isLE (a := a), ← Std.compare_isGE (a := a),
      Ordering.eq_eq_iff_isLE_and_isGE]

end FactoryInstances

/--
This structure contains all the data needed to create a `LinearPreorderPackage α` instance.
Its fields are automatically provided if possible. For the detailed rules how the fields are
inferred, see `LinearPreorderPackage.ofOrd`.
-/
public structure Packages.LinearPreorderOfOrdArgs (α : Type u) where
  ord : Ord α := by infer_instance
  transOrd  : TransOrd α := by infer_instance
  le [i : Ord α] (hi : i = ord := by rfl) :
      LE α := by
    intro i hi
    first
      | infer_instance
      | exact FactoryInstances.instLEOfOrd
  lawful_le [i : Ord α] (hi : i = ord := by rfl) [o : OrientedOrd α]
      [il : LE α] (hil : il = le hi := by rfl) :
      LawfulOrderOrd α := by
    intro i hi o il hil
    letI := i
    cases hi
    letI := il
    cases hil
    first
      | infer_instance
      | exact FactoryInstances.instLawfulOrderOrdOfOrd
  decidableLE [i : Ord α] (hi : i = ord := by rfl) [il : LE α] (hil : il = le hi := by rfl)
      (l : LawfulOrderOrd α) :
      DecidableLE α := by
    intro i hi il hil
    letI := i
    cases hi
    letI := il
    cases hil
    first
      | infer_instance
      | exact FactoryInstances.instDecidableLEOfOrd
  lt [i : Ord α] (hi : i = ord := by rfl) :
      LT α := by
    intro i hi
    first
      | infer_instance
      | exact FactoryInstances.instLTOfOrd
  lawful_lt [i : Ord α] (hi : i = ord := by rfl)
      [ile : LE α] (hile : ile = le hi := by rfl) (l : LawfulOrderOrd α)
      [ilt : LT α] (hilt : ilt = lt hi := by rfl) :
      ∀ a b : α, a < b ↔ compare a b = .lt := by
    intro i hi ile hile l ilt hilt a b
    letI := i
    cases hi
    letI := ile
    cases hile
    letI := ilt
    cases hilt
    exact Std.compare_eq_lt.symm
  decidableLT [i : Ord α] (hi : i = ord := by rfl) [ilt : LT α] (hilt : ilt = lt hi := by rfl)
      [ile : LE α] (hile : ile = le hi := by rfl) (lo : LawfulOrderOrd α)
      (l : ∀ a b : α, a < b ↔ compare a b = .lt) :
      DecidableLT α := by
    intro i hi ilt hilt ile hile lo
    letI := i
    cases hi
    letI := ilt
    cases hilt
    letI := ile
    cases hile
    first
      | infer_instance
      | exact FactoryInstances.instDecidableLTOfOrd
  beq [i : Ord α] (hi : i = ord := by rfl) : BEq α := by
    first
      | infer_instance
      | exact fun _ => FactoryInstances.instBEqOfOrd
  lawful_beq [i : Ord α] (hi : i = ord := by rfl)
      [ile : LE α] (hile : ile = le hi := by rfl) (l : LawfulOrderOrd α)
      [ilt : BEq α] (hilt : ilt = beq hi := by rfl) :
      ∀ a b : α, a == b ↔ compare a b = .eq := by
    intro i hi ile hile l ilt hilt a b
    letI := i
    cases hi
    letI := ile
    cases hile
    letI := ilt
    cases hilt
    exact Std.compare_eq_eq.symm

@[expose]
public def LinearPreorderPackage.ofOrd (α : Type u)
    (args : Packages.LinearPreorderOfOrdArgs α := by exact {}) : LinearPreorderPackage α :=
  letI := args.ord
  haveI := args.transOrd
  letI := args.le
  letI := args.lt
  letI := args.beq
  haveI : LawfulOrderOrd α := args.lawful_le
  { toOrd := args.ord
    toLE := args.le
    toLT := args.lt
    toBEq := args.beq
    toLawfulOrderOrd := args.lawful_le
    lt_iff a b := by
      cases h : compare a b
      all_goals simp [h, ← args.lawful_le.compare_isLE a _, ← args.lawful_le.compare_isGE a _,
        args.lawful_lt (l := args.lawful_le)]
    beq_iff_le_and_ge a b := by
      simp [args.lawful_beq (l := args.lawful_le), Ordering.eq_eq_iff_isLE_and_isGE, compare_isLE,
        compare_isGE]
    decidableLE := args.decidableLE (l := args.lawful_le)
    decidableLT := args.decidableLT (l := args.lawful_lt (l := args.lawful_le)) (lo := args.lawful_le)
    le_refl a := by simp [← compare_isLE]
    le_total a b := by cases h : compare a b <;> simp [h, ← compare_isLE (a := a), ← compare_isGE (a := a)]
    le_trans a b c := by simpa [← compare_isLE] using TransOrd.isLE_trans }

end LinearPreorder

section LinearOrder

namespace FactoryInstances

public scoped instance instMinOfOrd {α : Type u} [Ord α] :
    Min α where
  min a b := if (compare a b).isLE then a else b

public scoped instance instMaxOfOrd {α : Type u} [Ord α] :
    Max α where
  max a b := if (compare b a).isLE then a else b

public instance instLawfulOrderLeftLeaningMinOfOrd {α : Type u} [Ord α] [LE α] [LawfulOrderOrd α] :
    LawfulOrderLeftLeaningMin α where
  min_eq_left a b := by simp +contextual only [← Std.compare_isLE, min, ↑reduceIte, implies_true]
  min_eq_right a b := by
    simp +contextual only [← Std.compare_isLE, min, Bool.false_eq_true, ↑reduceIte, implies_true]

public instance instLawfulOrderLeftLeaningMaxOfOrd {α : Type u} [Ord α] [LE α] [LawfulOrderOrd α] :
    LawfulOrderLeftLeaningMax α where
  max_eq_left a b := by simp +contextual only [← Std.compare_isLE, max, ↑reduceIte, implies_true]
  max_eq_right a b := by
    simp +contextual only [← Std.compare_isLE, max, Bool.false_eq_true, ↑reduceIte, implies_true]

end FactoryInstances

public structure Packages.LinearOrderOfOrdArgs (α : Type u) extends
    LinearPreorderOfOrdArgs α where
  eq_of_compare [i : Ord α] (hi : i = ord := by rfl) [ile : LE α] (hile : ile = le hi) :
      ∀ a b : α, compare a b = .eq → a = b := by
    intro i hi ile hile a b
    letI := i
    cases hi
    letI := ile
    cases hile
    first
    | exact LawfulEqOrd.eq_of_compare
  min [i : Ord α] (hi : i = ord := by rfl) : Min α := by
    intro i hi
    first
    | infer_instance
    | exact FactoryInstances.instMinOfOrd
  max [i : Ord α] (hi : i = ord := by rfl) : Max α := by
    intro i hi
    first
    | infer_instance
    | exact FactoryInstances.instMaxOfOrd
  min_eq [i : Ord α] (hi : i = ord := by rfl) [ile : LE α] (hile : ile = le hi := by rfl)
      [im : Min α] (him : im = min hi := by rfl) [LawfulOrderOrd α] :
      letI := min hi
      ∀ a b : α, Min.min a b = if (compare a b).isLE then a else b := by
    intro i hi ile hile im him _ a b
    letI := i
    cases hi
    letI := ile
    cases hile
    letI := im
    cases him
    first
      | exact Std.min_eq_if_compare_isLE (a := a) (b := b)
      | fail "Failed to automatically prove that `min` is left-leaning. Provide `min_eq` manually."
  max_eq [i : Ord α] (hi : i = ord := by rfl) [ile : LE α] (hile : ile = le hi := by rfl)
      [im : Max α] (him : im = max hi := by rfl) [LawfulOrderOrd α] :
      letI := max hi
      ∀ a b : α, Max.max a b = if (compare a b).isGE then a else b := by
    intro i hi ile hile im him _ a b
    letI := i
    cases hi
    letI := ile
    cases hile
    letI := im
    cases him
    first
      | exact Std.max_eq_if_compare_isGE (a := a) (b := b)
      | fail "Failed to automatically prove that `max` is left-leaning. Provide `max_eq` manually."

@[expose]
public def LinearOrderPackage.ofOrd (α : Type u)
    (args : Packages.LinearOrderOfOrdArgs α := by exact {}) : LinearOrderPackage α :=
  letI := args.ord
  letI := LinearPreorderPackage.ofOrd α args.toLinearPreorderOfOrdArgs
  haveI : LawfulEqOrd α := ⟨args.eq_of_compare rfl rfl _ _⟩
  letI : Min α := args.min
  letI : Max α := args.max
  { toMin := args.min
    toMax := args.max,
    le_antisymm := Antisymm.antisymm
    toLawfulOrderMin := IsLinearPreorder.lawfulOrderMin_of_min_eq
        (by simpa [compare_isLE] using args.min_eq)
    toLawfulOrderMax := IsLinearPreorder.lawfulOrderMax_of_max_eq
        (by simpa [compare_isGE] using args.max_eq) }

end LinearOrder

end Std

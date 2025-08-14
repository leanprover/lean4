module

prelude
public import Init.Data.Order.FactoriesExtra
public import Init.Data.Order.LemmasExtra

namespace Std

section Preorder

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

end Preorder

end Std

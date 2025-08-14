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

end FactoryInstances

#check compare_eq_lt

/--
This structure contains all the data needed to create a `PreorderPackage α` instance. Its fields
are automatically provided if possible. For the detailed rules how the fields are inferred, see
`PreorderPackage.ofLE`.
-/
public structure Packages.PreorderOfOrdArgs (α : Type u) where
  ord : Ord α := by infer_instance
  oriented_ord [i : Ord α] (hi : i = ord := by rfl) :
      ∀ a b : α, compare a b = .gt ↔ compare b a = .lt := by
    intro i hi
    letI := i
    cases hi
    first
      | exact OrientedCmp.gt_iff_lt (cmp := compare)
      | fail "Found no `OrientedOrd` instance. Please provide `oriented_ord` manually."
  le [i : Ord α] (hi : i = ord := by rfl) :
      LE α := by
    intro i hi
    first
      | infer_instance
      | exact FactoryInstances.instLEOfOrd
  lawful_le [i : Ord α] (hi : i = ord := by rfl) (o : ∀ a b : α, compare a b = .gt ↔ compare b a = .lt)
      [il : LE α] (hil : il = le hi := by rfl) :
      LawfulOrderOrd α := by
    intro i hi o il hil
    letI := i
    cases hi
    letI := il
    cases hil
    haveI := OrientedCmp.of_gt_iff_lt (cmp := compare) o
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
      (o : ∀ a b : α, compare a b = .gt ↔ compare b a = .lt)
      [ile : LE α] (hile : ile = le hi := by rfl) (l : LawfulOrderOrd α)
      [ilt : LT α] (hilt : ilt = lt hi := by rfl) :
      ∀ a b : α, a < b ↔ compare a b = .lt := by
    intro i hi o ilt hilt
    letI := i
    cases hi
    letI := ile
    cases hile
    letI := ilt
    cases hilt
    -- TODO
    -- inferring LawfulOrderLE
    -- proving manually
    haveI := OrientedCmp.of_gt_iff_lt (cmp := compare) o
    first
      | infer_instance
      | exact FactoryInstances.instLawfulOrderOrdOfOrd
  decidableLT [i : Ord α] (hi : i = ord := by rfl) [il : LT α] (hil : il = lt hi := by rfl)
      (l : ∀ a b : α, a < b ↔ compare a b = .lt) :
      DecidableLT α := by
    intro i hi il hil
    letI := i
    cases hi
    letI := il
    cases hil
    -- TODO
    first
      | infer_instance
      | exact FactoryInstances.instDecidableLEOfOrd
  -- lt [i : LE α] (hi : i = le := by rfl) : LT α := by
  --   first
  --     | infer_instance
  --     | exact fun _ => Classical.Order.instLT
  -- beq [i : LE α] [di : DecidableLE α] (hi : i = le := by rfl) : BEq α := by
  --   first
  --     | infer_instance
  --     | exact fun _ => FactoryInstances.instBEqOfDecidableLE
  -- lawful_lt [i : LE α] (hi : i = le := by rfl) :
  --   letI := lt hi; ∀ a b : α, a < b ↔ a ≤ b ∧ ¬ b ≤ a := by
  --   intro i hi
  --   first
  --     | simp only [Classical.Order.instLT, implies_true]; done -- use LawfulOrderLT?
  --     | fail "Failed to automatically prove that the `OrderData` and `LT` instances are compatible."
  -- decidableLT [i : LE α] (hi : i = le := by rfl)
  --     [d : DecidableLE α] (hd : d = hi ▸ decidableLE := by rfl)
  --     (l : haveI := lt hi; ∀ a b : α, a < b ↔ a ≤ b ∧ ¬ b ≤ a) :
  --     haveI := lt hi; DecidableLT α := by
  --   intro i hi d hd l
  --   letI := i
  --   cases hi
  --   letI := d
  --   cases hd
  --   haveI := @LawfulOrderLT.mk (lt_iff := l) ..
  --   first
  --     | infer_instance
  --     | exact FactoryInstances.instDecidableLTOfLE
  --     -- | fail "Failed to automatically derive a `DecidableLT` instance."
  -- lawful_beq [i : LE α] [DecidableLE α] (hi : i = le := by rfl) :
  --   letI := beq hi; ∀ a b : α, a == b ↔ a ≤ b ∧ b ≤ a := by
  --   intro i di hi
  --   first
  --     | simpa only [FactoryInstances.instBEqOfDecidableLE, BEq.beq] using fun a b =>
  --         Std.FactoryInstances.beq_iff; done
  --     | fail "Failed to automatically prove that the `OrderData` and `BEq` instances are compatible."
  -- le_refl [i : LE α] (hi : i = le := by rfl) : ∀ a : α, a ≤ a := by
  --   intro i hi
  --   cases hi
  --   first
  --     | exact Std.Refl.refl (r := (· ≤ ·))
  --     | fail "Failed to automatically prove that the `LE` instance is reflexive."
  -- le_trans [i : LE α] (hi : i = le := by rfl) :
  --     ∀ a b c : α, a ≤ b → b ≤ c → a ≤ c := by
  --   intro i hi
  --   letI := i
  --   cases hi
  --   first
  --     | exact fun _ _ _ hab hbc => Trans.trans (r := (· ≤ ·)) (s := (· ≤ ·)) (t := (· ≤ ·)) hab hbc
  --     | fail "Failed to automatically prove that the `LE` instance is transitive."

end Preorder

end Std

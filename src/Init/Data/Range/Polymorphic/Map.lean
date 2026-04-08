/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

prelude
public import Init.Data.Function
import Init.Data.Order.Lemmas
import Init.Data.Option.Function
public import Init.Data.Range.Polymorphic.Basic
import Init.Data.Option.Lemmas

public section

/-!
# Mappings between `UpwardEnumerable` types

In this file we build machinery for pulling back lawfulness properties for `UpwardEnumerable` along
injective functions that commute with the relevant operations.
-/

namespace Std

namespace PRange

namespace UpwardEnumerable

/--
An injective mapping between two types implementing `UpwardEnumerable` that commutes with `succ?`
and `succMany?`.

Having such a mapping means that all of the `Prop`-valued lawfulness classes around
`UpwardEnumerable` can be pulled back.
-/
structure Map (α : Type u) (β : Type v) [UpwardEnumerable α] [UpwardEnumerable β] where
  toFun : α → β
  injective : Function.Injective toFun
  succ?_toFun (a : α) : succ? (toFun a) = (succ? a).map toFun
  succMany?_toFun (n : Nat) (a : α) : succMany? n (toFun a) = (succMany? n a).map toFun

namespace Map

variable [UpwardEnumerable α] [UpwardEnumerable β]

theorem succ?_eq_none_iff (f : Map α β) {a : α} :
    succ? a = none ↔ succ? (f.toFun a) = none := by
  rw [← (Option.map_injective f.injective).eq_iff, Option.map_none, ← f.succ?_toFun]

theorem succ?_eq_some_iff (f : Map α β) {a b : α} :
    succ? a = some b ↔ succ? (f.toFun a) = some (f.toFun b) := by
  rw [← (Option.map_injective f.injective).eq_iff, Option.map_some, ← f.succ?_toFun]

theorem le_iff (f : Map α β) {a b : α} :
    UpwardEnumerable.LE a b ↔ UpwardEnumerable.LE (f.toFun a) (f.toFun b) := by
  simp only [UpwardEnumerable.LE, f.succMany?_toFun, Option.map_eq_some_iff]
  refine ⟨fun ⟨n, hn⟩ => ⟨n, b, by simp [hn]⟩, fun ⟨n, c, hn⟩ => ⟨n, ?_⟩⟩
  rw [hn.1, Option.some_inj, f.injective hn.2]

theorem lt_iff (f : Map α β) {a b : α} :
    UpwardEnumerable.LT a b ↔ UpwardEnumerable.LT (f.toFun a) (f.toFun b) := by
  simp only [UpwardEnumerable.LT, f.succMany?_toFun, Option.map_eq_some_iff]
  refine ⟨fun ⟨n, hn⟩ => ⟨n, b, by simp [hn]⟩, fun ⟨n, c, hn⟩ => ⟨n, ?_⟩⟩
  rw [hn.1, Option.some_inj, f.injective hn.2]

theorem succ?_toFun' (f : Map α β) : succ? ∘ f.toFun = Option.map f.toFun ∘ succ? := by
  ext
  simp [f.succ?_toFun]

/-- Compatibility class for `Map` and `≤`. -/
class PreservesLE [LE α] [LE β] (f : Map α β) where
  le_iff : a ≤ b ↔ f.toFun a ≤ f.toFun b

/-- Compatibility class for `Map` and `<`. -/
class PreservesLT [LT α] [LT β] (f : Map α β) where
  lt_iff : a < b ↔ f.toFun a < f.toFun b

/-- Compatibility class for `Map` and `Rxc.HasSize`. -/
class PreservesRxcSize [Rxc.HasSize α] [Rxc.HasSize β] (f : Map α β) where
  size_eq : Rxc.HasSize.size a b = Rxc.HasSize.size (f.toFun a) (f.toFun b)

/-- Compatibility class for `Map` and `Rxo.HasSize`. -/
class PreservesRxoSize [Rxo.HasSize α] [Rxo.HasSize β] (f : Map α β) where
  size_eq : Rxo.HasSize.size a b = Rxo.HasSize.size (f.toFun a) (f.toFun b)

/-- Compatibility class for `Map` and `Rxi.HasSize`. -/
class PreservesRxiSize [Rxi.HasSize α] [Rxi.HasSize β] (f : Map α β) where
  size_eq : Rxi.HasSize.size b = Rxi.HasSize.size (f.toFun b)

/-- Compatibility class for `Map` and `Least?`. -/
class PreservesLeast? [Least? α] [Least? β] (f : Map α β) where
  map_least? : Least?.least?.map f.toFun = Least?.least?

end UpwardEnumerable.Map

open UpwardEnumerable

variable [UpwardEnumerable α] [UpwardEnumerable β]

theorem LawfulUpwardEnumerable.ofMap [LawfulUpwardEnumerable β] (f : Map α β) :
    LawfulUpwardEnumerable α where
  ne_of_lt a b := by
    simpa only [f.lt_iff, ← f.injective.ne_iff] using LawfulUpwardEnumerable.ne_of_lt _ _
  succMany?_zero a := by
    apply Option.map_injective f.injective
    simpa [← f.succMany?_toFun] using LawfulUpwardEnumerable.succMany?_zero _
  succMany?_add_one n a := by
    apply Option.map_injective f.injective
    rw [← f.succMany?_toFun, LawfulUpwardEnumerable.succMany?_add_one,
      f.succMany?_toFun, Option.bind_map, Map.succ?_toFun', Option.map_bind]

instance [LE α] [LT α] [LawfulOrderLT α] [LE β] [LT β] [LawfulOrderLT β] (f : Map α β)
    [f.PreservesLE] : f.PreservesLT where
  lt_iff := by simp [lt_iff_le_and_not_ge, Map.PreservesLE.le_iff (f := f)]

theorem LawfulUpwardEnumerableLE.ofMap [LE α] [LE β] [LawfulUpwardEnumerableLE β] (f : Map α β)
    [f.PreservesLE] : LawfulUpwardEnumerableLE α where
  le_iff := by simp [Map.PreservesLE.le_iff (f := f), f.le_iff, LawfulUpwardEnumerableLE.le_iff]

theorem LawfulUpwardEnumerableLT.ofMap [LT α] [LT β] [LawfulUpwardEnumerableLT β] (f : Map α β)
    [f.PreservesLT] : LawfulUpwardEnumerableLT α where
  lt_iff := by simp [Map.PreservesLT.lt_iff (f := f), f.lt_iff, LawfulUpwardEnumerableLT.lt_iff]

theorem LawfulUpwardEnumerableLeast?.ofMap [Least? α] [Least? β] [LawfulUpwardEnumerableLeast? β]
    (f : Map α β) [f.PreservesLeast?] : LawfulUpwardEnumerableLeast? α where
  least?_le a := by
    obtain ⟨l, hl, hl'⟩ := LawfulUpwardEnumerableLeast?.least?_le (f.toFun a)
    have : (Least?.least? (α := α)).isSome := by
      rw [← Option.isSome_map (f := f.toFun), Map.PreservesLeast?.map_least?,
        hl, Option.isSome_some]
    refine ⟨Option.get _ this, by simp, ?_⟩
    rw [f.le_iff, Option.apply_get (f := f.toFun)]
    simpa [Map.PreservesLeast?.map_least?, hl] using hl'

end PRange

open PRange PRange.UpwardEnumerable

variable [UpwardEnumerable α] [UpwardEnumerable β]

theorem Rxc.LawfulHasSize.ofMap [LE α] [LE β] [Rxc.HasSize α] [Rxc.HasSize β] [Rxc.LawfulHasSize β]
    (f : Map α β) [f.PreservesLE] [f.PreservesRxcSize] : Rxc.LawfulHasSize α where
  size_eq_zero_of_not_le a b := by
    simpa [Map.PreservesRxcSize.size_eq (f := f), Map.PreservesLE.le_iff (f := f)] using
      Rxc.LawfulHasSize.size_eq_zero_of_not_le _ _
  size_eq_one_of_succ?_eq_none lo hi := by
    simpa [Map.PreservesRxcSize.size_eq (f := f), Map.PreservesLE.le_iff (f := f),
        f.succ?_eq_none_iff] using
      Rxc.LawfulHasSize.size_eq_one_of_succ?_eq_none _ _
  size_eq_succ_of_succ?_eq_some lo hi lo' := by
    simpa [Map.PreservesRxcSize.size_eq (f := f), Map.PreservesLE.le_iff (f := f),
        f.succ?_eq_some_iff] using
      Rxc.LawfulHasSize.size_eq_succ_of_succ?_eq_some _ _ _

theorem Rxo.LawfulHasSize.ofMap [LT α] [LT β] [Rxo.HasSize α] [Rxo.HasSize β] [Rxo.LawfulHasSize β]
    (f : Map α β) [f.PreservesLT] [f.PreservesRxoSize] : Rxo.LawfulHasSize α where
  size_eq_zero_of_not_le a b := by
    simpa [Map.PreservesRxoSize.size_eq (f := f), Map.PreservesLT.lt_iff (f := f)] using
      Rxo.LawfulHasSize.size_eq_zero_of_not_le _ _
  size_eq_one_of_succ?_eq_none lo hi := by
    simpa [Map.PreservesRxoSize.size_eq (f := f), Map.PreservesLT.lt_iff (f := f),
        f.succ?_eq_none_iff] using
      Rxo.LawfulHasSize.size_eq_one_of_succ?_eq_none _ _
  size_eq_succ_of_succ?_eq_some lo hi lo' := by
    simpa [Map.PreservesRxoSize.size_eq (f := f), Map.PreservesLT.lt_iff (f := f),
        f.succ?_eq_some_iff] using
      Rxo.LawfulHasSize.size_eq_succ_of_succ?_eq_some _ _ _

theorem Rxi.LawfulHasSize.ofMap [Rxi.HasSize α] [Rxi.HasSize β] [Rxi.LawfulHasSize β]
    (f : Map α β) [f.PreservesRxiSize] : Rxi.LawfulHasSize α where
  size_eq_one_of_succ?_eq_none lo := by
    simpa [Map.PreservesRxiSize.size_eq (f := f), f.succ?_eq_none_iff] using
      Rxi.LawfulHasSize.size_eq_one_of_succ?_eq_none _
  size_eq_succ_of_succ?_eq_some lo lo' := by
    simpa [Map.PreservesRxiSize.size_eq (f := f), f.succ?_eq_some_iff] using
      Rxi.LawfulHasSize.size_eq_succ_of_succ?_eq_some _ _

theorem Rxc.IsAlwaysFinite.ofMap [LE α] [LE β] [Rxc.IsAlwaysFinite β] (f : Map α β)
    [f.PreservesLE] : Rxc.IsAlwaysFinite α where
  finite init hi := by
    obtain ⟨n, hn⟩ := Rxc.IsAlwaysFinite.finite (f.toFun init) (f.toFun hi)
    exact ⟨n, by simpa [f.succMany?_toFun, Map.PreservesLE.le_iff (f := f)] using hn⟩

theorem Rxo.IsAlwaysFinite.ofMap [LT α] [LT β] [Rxo.IsAlwaysFinite β] (f : Map α β)
    [f.PreservesLT] : Rxo.IsAlwaysFinite α where
  finite init hi := by
    obtain ⟨n, hn⟩ := Rxo.IsAlwaysFinite.finite (f.toFun init) (f.toFun hi)
    exact ⟨n, by simpa [f.succMany?_toFun, Map.PreservesLT.lt_iff (f := f)] using hn⟩

theorem Rxi.IsAlwaysFinite.ofMap [Rxi.IsAlwaysFinite β] (f : Map α β) : Rxi.IsAlwaysFinite α where
  finite init := by
    obtain ⟨n, hn⟩ := Rxi.IsAlwaysFinite.finite (f.toFun init)
    exact ⟨n, by simpa [f.succMany?_toFun] using hn⟩

end Std

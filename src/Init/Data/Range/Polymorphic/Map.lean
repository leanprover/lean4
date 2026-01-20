/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

prelude
public import Init.Data.Range.Polymorphic.Instances
public import Init.Data.Function
import Init.Data.Order.Lemmas

public section

theorem Option.map_injective {f : α → β} (hf : Function.Injective f) :
    Function.Injective (Option.map f) := by
  intros a b hab
  cases a <;> cases b <;> simp_all <;> exact hf hab

@[simp]
theorem Option.elim_map {f : α → β} {g' : γ} {g : β → γ} (o : Option α) :
    (o.map f).elim g' g = o.elim g' (g ∘ f) := by
  cases o <;> simp

namespace Std.PRange.UpwardEnumerable

structure Map (α : Type u) (β : Type v) [UpwardEnumerable α] [UpwardEnumerable β] where
  toFun : α → β
  injective : Function.Injective toFun
  succ?_toFun (a : α) : succ? (toFun a) = (succ? a).map toFun
  succMany?_toFun (n : Nat) (a : α) : succMany? n (toFun a) = (succMany? n a).map toFun

variable [UpwardEnumerable α] [UpwardEnumerable β]

theorem Map.succ?_eq_none_iff (f : Map α β) {a : α} :
    succ? a = none ↔ succ? (f.toFun a) = none := by
  rw [← (Option.map_injective f.injective).eq_iff, Option.map_none, ← f.succ?_toFun]

theorem Map.succ?_eq_some_iff (f : Map α β) {a b : α} :
    succ? a = some b ↔ succ? (f.toFun a) = some (f.toFun b) := by
  rw [← (Option.map_injective f.injective).eq_iff, Option.map_some, ← f.succ?_toFun]

theorem Map.le_iff (f : Map α β) {a b : α} :
    UpwardEnumerable.LE a b ↔ UpwardEnumerable.LE (f.toFun a) (f.toFun b) := by
  simp only [UpwardEnumerable.LE, f.succMany?_toFun, Option.map_eq_some_iff]
  refine ⟨fun ⟨n, hn⟩ => ⟨n, b, by simp [hn]⟩, fun ⟨n, c, hn⟩ => ⟨n, ?_⟩⟩
  rw [hn.1, Option.some_inj, f.injective hn.2]

theorem Map.lt_iff (f : Map α β) {a b : α} :
    UpwardEnumerable.LT a b ↔ UpwardEnumerable.LT (f.toFun a) (f.toFun b) := by
  simp only [UpwardEnumerable.LT, f.succMany?_toFun, Option.map_eq_some_iff]
  refine ⟨fun ⟨n, hn⟩ => ⟨n, b, by simp [hn]⟩, fun ⟨n, c, hn⟩ => ⟨n, ?_⟩⟩
  rw [hn.1, Option.some_inj, f.injective hn.2]

theorem Map.succ?_toFun' (f : Map α β) : succ? ∘ f.toFun = Option.map f.toFun ∘ succ? := by
  ext
  simp [f.succ?_toFun]

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

class Map.PreservesLE [LE α] [LE β] (f : Map α β) where
  le_iff : a ≤ b ↔ f.toFun a ≤ f.toFun b

class Map.PreservesLT [LT α] [LT β] (f : Map α β) where
  lt_iff : a < b ↔ f.toFun a < f.toFun b

instance [LE α] [LT α] [LawfulOrderLT α] [LE β] [LT β] [LawfulOrderLT β] (f : Map α β)
    [f.PreservesLE] : f.PreservesLT where
  lt_iff := by simp [lt_iff_le_and_not_ge, Map.PreservesLE.le_iff (f := f)]

theorem LawfulUpwardEnumerableLE.ofMap [LE α] [LE β] [LawfulUpwardEnumerableLE β] (f : Map α β)
    [f.PreservesLE] : LawfulUpwardEnumerableLE α where
  le_iff := by simp [Map.PreservesLE.le_iff (f := f), f.le_iff, LawfulUpwardEnumerableLE.le_iff]

theorem LawfulUpwardEnumerableLT.ofMap [LT α] [LT β] [LawfulUpwardEnumerableLT β] (f : Map α β)
    [Map.PreservesLT f] : LawfulUpwardEnumerableLT α where
  lt_iff := by simp [Map.PreservesLT.lt_iff (f := f), f.lt_iff, LawfulUpwardEnumerableLT.lt_iff]

class Map.PreservesRxcSize [Rxc.HasSize α] [Rxc.HasSize β] (f : Map α β) where
  size_eq : Rxc.HasSize.size a b = Rxc.HasSize.size (f.toFun a) (f.toFun b)

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

end Std.PRange.UpwardEnumerable

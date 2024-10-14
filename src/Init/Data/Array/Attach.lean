/-
Copyright (c) 2021 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner, Mario Carneiro
-/
prelude
import Init.Data.Array.Mem
import Init.Data.Array.Lemmas
import Init.Data.List.Attach

namespace Array

/--
Unsafe implementation of `attachWith`, taking advantage of the fact that the representation of
`Array {x // P x}` is the same as the input `Array α`.
-/
@[inline] private unsafe def attachWithImpl
    (xs : Array α) (P : α → Prop) (_ : ∀ x ∈ xs, P x) : Array {x // P x} := unsafeCast xs

/-- `O(1)`. "Attach" a proof `P x` that holds for all the elements of `xs` to produce a new array
  with the same elements but in the type `{x // P x}`. -/
@[implemented_by attachWithImpl] def attachWith
    (xs : Array α) (P : α → Prop) (H : ∀ x ∈ xs, P x) : Array {x // P x} :=
  ⟨xs.toList.attachWith P fun x h => H x (Array.Mem.mk h)⟩

/-- `O(1)`. "Attach" the proof that the elements of `xs` are in `xs` to produce a new array
  with the same elements but in the type `{x // x ∈ xs}`. -/
@[inline] def attach (xs : Array α) : Array {x // x ∈ xs} := xs.attachWith _ fun _ => id

@[simp] theorem _root_.List.attachWith_toArray {l : List α} {P : α → Prop} {H : ∀ x ∈ l.toArray, P x} :
    l.toArray.attachWith P H = (l.attachWith P (by simpa using H)).toArray := by
  simp [attachWith]

@[simp] theorem _root_.List.attach_toArray {l : List α} :
    l.toArray.attach = (l.attachWith (· ∈ l.toArray) (by simp)).toArray := by
  simp [attach]

@[simp] theorem toList_attachWith {l : Array α} {P : α → Prop} {H : ∀ x ∈ l, P x} :
   (l.attachWith P H).toList = l.toList.attachWith P (by simpa [mem_toList] using H) := by
  simp [attachWith]

@[simp] theorem toList_attach {α : Type _} {l : Array α} :
    l.attach.toList = l.toList.attachWith (· ∈ l) (by simp [mem_toList]) := by
  simp [attach]

/-! ## unattach

`Array.unattach` is the (one-sided) inverse of `Array.attach`. It is a synonym for `Array.map Subtype.val`.

We use it by providing a simp lemma `l.attach.unattach = l`, and simp lemmas which recognize higher order
functions applied to `l : Array { x // p x }` which only depend on the value, not the predicate, and rewrite these
in terms of a simpler function applied to `l.unattach`.

Further, we provide simp lemmas that push `unattach` inwards.
-/

/--
A synonym for `l.map (·.val)`. Mostly this should not be needed by users.
It is introduced as in intermediate step by lemmas such as `map_subtype`,
and is ideally subsequently simplified away by `unattach_attach`.

If not, usually the right approach is `simp [Array.unattach, -Array.map_subtype]` to unfold.
-/
def unattach {α : Type _} {p : α → Prop} (l : Array { x // p x }) := l.map (·.val)

@[simp] theorem unattach_nil {p : α → Prop} : (#[] : Array { x // p x }).unattach = #[] := rfl
@[simp] theorem unattach_push {p : α → Prop} {a : { x // p x }} {l : Array { x // p x }} :
    (l.push a).unattach = l.unattach.push a.1 := by
  simp only [unattach, Array.map_push]

@[simp] theorem size_unattach {p : α → Prop} {l : Array { x // p x }} :
    l.unattach.size = l.size := by
  unfold unattach
  simp

@[simp] theorem _root_.List.unattach_toArray {p : α → Prop} {l : List { x // p x }} :
    l.toArray.unattach = l.unattach.toArray := by
  simp only [unattach, List.map_toArray, List.unattach]

@[simp] theorem toList_unattach {p : α → Prop} {l : Array { x // p x }} :
    l.unattach.toList = l.toList.unattach := by
  simp only [unattach, toList_map, List.unattach]

@[simp] theorem unattach_attach {l : Array α} : l.attach.unattach = l := by
  cases l
  simp

@[simp] theorem unattach_attachWith {p : α → Prop} {l : Array α}
    {H : ∀ a ∈ l, p a} :
    (l.attachWith p H).unattach = l := by
  cases l
  simp

/-! ### Recognizing higher order functions using a function that only depends on the value. -/

/--
This lemma identifies folds over arrays of subtypes, where the function only depends on the value, not the proposition,
and simplifies these to the function directly taking the value.
-/
theorem foldl_subtype {p : α → Prop} {l : Array { x // p x }}
    {f : β → { x // p x } → β} {g : β → α → β} {x : β}
    {hf : ∀ b x h, f b ⟨x, h⟩ = g b x} :
    l.foldl f x = l.unattach.foldl g x := by
  cases l
  simp only [List.foldl_toArray', List.unattach_toArray]
  rw [List.foldl_subtype] -- Why can't simp do this?
  simp [hf]

/-- Variant of `foldl_subtype` with side condition to check `stop = l.size`. -/
@[simp] theorem foldl_subtype' {p : α → Prop} {l : Array { x // p x }}
    {f : β → { x // p x } → β} {g : β → α → β} {x : β}
    {hf : ∀ b x h, f b ⟨x, h⟩ = g b x} (h : stop = l.size) :
    l.foldl f x 0 stop = l.unattach.foldl g x := by
  subst h
  rwa [foldl_subtype]

/--
This lemma identifies folds over arrays of subtypes, where the function only depends on the value, not the proposition,
and simplifies these to the function directly taking the value.
-/
theorem foldr_subtype {p : α → Prop} {l : Array { x // p x }}
    {f : { x // p x } → β → β} {g : α → β → β} {x : β}
    {hf : ∀ x h b, f ⟨x, h⟩ b = g x b} :
    l.foldr f x = l.unattach.foldr g x := by
  cases l
  simp only [List.foldr_toArray', List.unattach_toArray]
  rw [List.foldr_subtype]
  simp [hf]

/-- Variant of `foldr_subtype` with side condition to check `stop = l.size`. -/
@[simp] theorem foldr_subtype' {p : α → Prop} {l : Array { x // p x }}
    {f : { x // p x } → β → β} {g : α → β → β} {x : β}
    {hf : ∀ x h b, f ⟨x, h⟩ b = g x b} (h : start = l.size) :
    l.foldr f x start 0 = l.unattach.foldr g x := by
  subst h
  rwa [foldr_subtype]

/--
This lemma identifies maps over arrays of subtypes, where the function only depends on the value, not the proposition,
and simplifies these to the function directly taking the value.
-/
@[simp] theorem map_subtype {p : α → Prop} {l : Array { x // p x }}
    {f : { x // p x } → β} {g : α → β} {hf : ∀ x h, f ⟨x, h⟩ = g x} :
    l.map f = l.unattach.map g := by
  cases l
  simp only [List.map_toArray, List.unattach_toArray]
  rw [List.map_subtype]
  simp [hf]

@[simp] theorem filterMap_subtype {p : α → Prop} {l : Array { x // p x }}
    {f : { x // p x } → Option β} {g : α → Option β} {hf : ∀ x h, f ⟨x, h⟩ = g x} :
    l.filterMap f = l.unattach.filterMap g := by
  cases l
  simp only [size_toArray, List.filterMap_toArray', List.unattach_toArray, List.length_unattach,
    mk.injEq]
  rw [List.filterMap_subtype]
  simp [hf]

@[simp] theorem unattach_filter {p : α → Prop} {l : Array { x // p x }}
    {f : { x // p x } → Bool} {g : α → Bool} {hf : ∀ x h, f ⟨x, h⟩ = g x} :
    (l.filter f).unattach = l.unattach.filter g := by
  cases l
  simp [hf]

/-! ### Simp lemmas pushing `unattach` inwards. -/

@[simp] theorem unattach_reverse {p : α → Prop} {l : Array { x // p x }} :
    l.reverse.unattach = l.unattach.reverse := by
  cases l
  simp

@[simp] theorem unattach_append {p : α → Prop} {l₁ l₂ : Array { x // p x }} :
    (l₁ ++ l₂).unattach = l₁.unattach ++ l₂.unattach := by
  cases l₁
  cases l₂
  simp

end Array

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

@[simp] theorem unattach_nil {α : Type _} {p : α → Prop} : (#[] : Array { x // p x }).unattach = #[] := rfl
@[simp] theorem unattach_push {α : Type _} {p : α → Prop} {a : { x // p x }} {l : Array { x // p x }} :
    (l.push a).unattach = l.unattach.push a.1 := by
  simp [unattach]

@[simp] theorem size_unattach {α : Type _} {p : α → Prop} {l : Array { x // p x }} :
    l.unattach.size = l.size := by
  unfold unattach
  simp

@[simp] theorem _root_.List.unattach_toArray {α : Type _} {p : α → Prop} {l : List { x // p x }} :
    l.toArray.unattach = l.unattach.toArray := by
  simp only [Array.unattach, List.map_toArray, List.unattach]

@[simp] theorem toList_unattach {α : Type _} {p : α → Prop} {l : Array { x // p x }} :
    l.unattach.toList = l.toList.unattach := by
  simp [unattach]

@[simp] theorem unattach_attach {α : Type _} (l : Array α) : l.attach.unattach = l := by
  cases l
  simp

@[simp] theorem unattach_attachWith {α : Type _} {p : α → Prop} {l : Array α}
    {H : ∀ a ∈ l, p a} :
    (l.attachWith p H).unattach = l := by
  cases l
  simp

/-! ### Recognizing higher order functions using a function that only depends on the value. -/

/--
This lemma identifies folds over arrays of subtypes, where the function only depends on the value, not the proposition,
and simplifies these to the function directly taking the value.
-/
@[simp] theorem foldl_subtype {p : α → Prop} {l : Array { x // p x }}
    {f : β → { x // p x } → β} {g : β → α → β} {x : β}
    {hf : ∀ b x, f b x = g b x.1} :
    l.foldl f x = l.unattach.foldl g x := by
  cases l
  simp [hf]

/--
This lemma identifies folds over arrays of subtypes, where the function only depends on the value, not the proposition,
and simplifies these to the function directly taking the value.
-/
@[simp] theorem foldr_subtype {p : α → Prop} {l : Array { x // p x }}
    {f : { x // p x } → β → β} {g : α → β → β} {x : β}
    {hf : ∀ x b, f x b = g x.1 b} :
    l.foldr f x = l.unattach.foldr g x := by
  cases l
  simp [hf]

/--
This lemma identifies maps over arrays of subtypes, where the function only depends on the value, not the proposition,
and simplifies these to the function directly taking the value.
-/
@[simp] theorem map_subtype {p : α → Prop} {l : Array { x // p x }}
    {f : { x // p x } → β} {g : α → β} {hf : ∀ x, f x = g x.1} :
    l.map f = l.unattach.map g := by
  cases l
  simp [hf]

@[simp] theorem filterMap_subtype {p : α → Prop} {l : Array { x // p x }}
    {f : { x // p x } → Option β} {g : α → Option β} {hf : ∀ x, f x = g x.1} :
    l.filterMap f = l.unattach.filterMap g := by
  cases l
  simp [hf]

@[simp] theorem filter_unattach {p : α → Prop} {l : Array { x // p x }}
    {f : { x // p x } → Bool} {g : α → Bool} {hf : ∀ x, f x = g x.1} :
    (l.filter f).unattach = l.unattach.filter g := by
  cases l
  simp [hf]

/-! ### Simp lemmas pushing `unattach` inwards. -/

@[simp] theorem reverse_unattach {p : α → Prop} {l : Array { x // p x }} :
    l.reverse.unattach = l.unattach.reverse := by
  cases l
  simp

@[simp] theorem append_unattach {p : α → Prop} {l₁ l₂ : Array { x // p x }} :
    (l₁ ++ l₂).unattach = l₁.unattach ++ l₂.unattach := by
  cases l₁
  cases l₂
  simp

end Array

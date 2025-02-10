/-
Copyright (c) 2021 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner, Mario Carneiro
-/
prelude
import Init.Data.Array.Mem
import Init.Data.Array.Lemmas
import Init.Data.Array.Count
import Init.Data.List.Attach

namespace Array

/--
`O(n)`. Partial map. If `f : Π a, P a → β` is a partial function defined on
`a : α` satisfying `P`, then `pmap f l h` is essentially the same as `map f l`
but is defined only when all members of `l` satisfy `P`, using the proof
to apply `f`.

We replace this at runtime with a more efficient version via the `csimp` lemma `pmap_eq_pmapImpl`.
-/
def pmap {P : α → Prop} (f : ∀ a, P a → β) (l : Array α) (H : ∀ a ∈ l, P a) : Array β :=
  (l.toList.pmap f (fun a m => H a (mem_def.mpr m))).toArray

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

@[simp] theorem _root_.List.pmap_toArray {l : List α} {P : α → Prop} {f : ∀ a, P a → β} {H : ∀ a ∈ l.toArray, P a} :
    l.toArray.pmap f H = (l.pmap f (by simpa using H)).toArray := by
  simp [pmap]

@[simp] theorem toList_attachWith {l : Array α} {P : α → Prop} {H : ∀ x ∈ l, P x} :
   (l.attachWith P H).toList = l.toList.attachWith P (by simpa [mem_toList] using H) := by
  simp [attachWith]

@[simp] theorem toList_attach {α : Type _} {l : Array α} :
    l.attach.toList = l.toList.attachWith (· ∈ l) (by simp [mem_toList]) := by
  simp [attach]

@[simp] theorem toList_pmap {l : Array α} {P : α → Prop} {f : ∀ a, P a → β} {H : ∀ a ∈ l, P a} :
    (l.pmap f H).toList = l.toList.pmap f (fun a m => H a (mem_def.mpr m)) := by
  simp [pmap]

/-- Implementation of `pmap` using the zero-copy version of `attach`. -/
@[inline] private def pmapImpl {P : α → Prop} (f : ∀ a, P a → β) (l : Array α) (H : ∀ a ∈ l, P a) :
    Array β := (l.attachWith _ H).map fun ⟨x, h'⟩ => f x h'

@[csimp] private theorem pmap_eq_pmapImpl : @pmap = @pmapImpl := by
  funext α β p f L h'
  cases L
  simp only [pmap, pmapImpl, List.attachWith_toArray, List.map_toArray, mk.injEq, List.map_attachWith_eq_pmap]
  apply List.pmap_congr_left
  intro a m h₁ h₂
  congr

@[simp] theorem pmap_empty {P : α → Prop} (f : ∀ a, P a → β) : pmap f #[] (by simp) = #[] := rfl

@[simp] theorem pmap_push {P : α → Prop} (f : ∀ a, P a → β) (a : α) (l : Array α) (h : ∀ b ∈ l.push a, P b) :
    pmap f (l.push a) h =
      (pmap f l (fun a m => by simp at h; exact h a (.inl m))).push (f a (h a (by simp))) := by
  simp [pmap]

@[simp] theorem attach_empty : (#[] : Array α).attach = #[] := rfl

@[simp] theorem attachWith_empty {P : α → Prop} (H : ∀ x ∈ #[], P x) : (#[] : Array α).attachWith P H = #[] := rfl

@[simp] theorem _root_.List.attachWith_mem_toArray {l : List α} :
    l.attachWith (fun x => x ∈ l.toArray) (fun x h => by simpa using h) =
      l.attach.map fun ⟨x, h⟩ => ⟨x, by simpa using h⟩ := by
  simp only [List.attachWith, List.attach, List.map_pmap]
  apply List.pmap_congr_left
  simp

@[simp]
theorem pmap_eq_map (p : α → Prop) (f : α → β) (l : Array α) (H) :
    @pmap _ _ p (fun a _ => f a) l H = map f l := by
  cases l; simp

theorem pmap_congr_left {p q : α → Prop} {f : ∀ a, p a → β} {g : ∀ a, q a → β} (l : Array α) {H₁ H₂}
    (h : ∀ a ∈ l, ∀ (h₁ h₂), f a h₁ = g a h₂) : pmap f l H₁ = pmap g l H₂ := by
  cases l
  simp only [mem_toArray] at h
  simp only [List.pmap_toArray, mk.injEq]
  rw [List.pmap_congr_left _ h]

theorem map_pmap {p : α → Prop} (g : β → γ) (f : ∀ a, p a → β) (l H) :
    map g (pmap f l H) = pmap (fun a h => g (f a h)) l H := by
  cases l
  simp [List.map_pmap]

theorem pmap_map {p : β → Prop} (g : ∀ b, p b → γ) (f : α → β) (l H) :
    pmap g (map f l) H = pmap (fun a h => g (f a) h) l fun _ h => H _ (mem_map_of_mem _ h) := by
  cases l
  simp [List.pmap_map]

theorem attach_congr {l₁ l₂ : Array α} (h : l₁ = l₂) :
    l₁.attach = l₂.attach.map (fun x => ⟨x.1, h ▸ x.2⟩) := by
  subst h
  simp

theorem attachWith_congr {l₁ l₂ : Array α} (w : l₁ = l₂) {P : α → Prop} {H : ∀ x ∈ l₁, P x} :
    l₁.attachWith P H = l₂.attachWith P fun _ h => H _ (w ▸ h) := by
  subst w
  simp

@[simp] theorem attach_push {a : α} {l : Array α} :
    (l.push a).attach =
      (l.attach.map (fun ⟨x, h⟩ => ⟨x, mem_push_of_mem a h⟩)).push ⟨a, by simp⟩ := by
  cases l
  rw [attach_congr (List.push_toArray _ _)]
  simp [Function.comp_def]

@[simp] theorem attachWith_push {a : α} {l : Array α} {P : α → Prop} {H : ∀ x ∈ l.push a, P x} :
    (l.push a).attachWith P H =
      (l.attachWith P (fun x h => by simp at H; exact H x (.inl h))).push ⟨a, H a (by simp)⟩ := by
  cases l
  simp [attachWith_congr (List.push_toArray _ _)]

theorem pmap_eq_map_attach {p : α → Prop} (f : ∀ a, p a → β) (l H) :
    pmap f l H = l.attach.map fun x => f x.1 (H _ x.2) := by
  cases l
  simp [List.pmap_eq_map_attach]

@[simp]
theorem pmap_eq_attachWith {p q : α → Prop} (f : ∀ a, p a → q a) (l H) :
    pmap (fun a h => ⟨a, f a h⟩) l H = l.attachWith q (fun x h => f x (H x h)) := by
  cases l
  simp [List.pmap_eq_attachWith]

theorem attach_map_coe (l : Array α) (f : α → β) :
    (l.attach.map fun (i : {i // i ∈ l}) => f i) = l.map f := by
  cases l
  simp

theorem attach_map_val (l : Array α) (f : α → β) : (l.attach.map fun i => f i.val) = l.map f :=
  attach_map_coe _ _

theorem attach_map_subtype_val (l : Array α) : l.attach.map Subtype.val = l := by
  cases l; simp

theorem attachWith_map_coe {p : α → Prop} (f : α → β) (l : Array α) (H : ∀ a ∈ l, p a) :
    ((l.attachWith p H).map fun (i : { i // p i}) => f i) = l.map f := by
  cases l; simp

theorem attachWith_map_val {p : α → Prop} (f : α → β) (l : Array α) (H : ∀ a ∈ l, p a) :
    ((l.attachWith p H).map fun i => f i.val) = l.map f :=
  attachWith_map_coe _ _ _

theorem attachWith_map_subtype_val {p : α → Prop} (l : Array α) (H : ∀ a ∈ l, p a) :
    (l.attachWith p H).map Subtype.val = l := by
  cases l; simp

@[simp]
theorem mem_attach (l : Array α) : ∀ x, x ∈ l.attach
  | ⟨a, h⟩ => by
    have := mem_map.1 (by rw [attach_map_subtype_val] <;> exact h)
    rcases this with ⟨⟨_, _⟩, m, rfl⟩
    exact m

@[simp]
theorem mem_attachWith (l : Array α) {q : α → Prop} (H) (x : {x // q x}) :
    x ∈ l.attachWith q H ↔ x.1 ∈ l := by
  cases l
  simp

@[simp]
theorem mem_pmap {p : α → Prop} {f : ∀ a, p a → β} {l H b} :
    b ∈ pmap f l H ↔ ∃ (a : _) (h : a ∈ l), f a (H a h) = b := by
  simp only [pmap_eq_map_attach, mem_map, mem_attach, true_and, Subtype.exists, eq_comm]

theorem mem_pmap_of_mem {p : α → Prop} {f : ∀ a, p a → β} {l H} {a} (h : a ∈ l) :
    f a (H a h) ∈ pmap f l H := by
  rw [mem_pmap]
  exact ⟨a, h, rfl⟩

@[simp]
theorem size_pmap {p : α → Prop} {f : ∀ a, p a → β} {l H} : (pmap f l H).size = l.size := by
  cases l; simp

@[simp]
theorem size_attach {L : Array α} : L.attach.size = L.size := by
  cases L; simp

@[simp]
theorem size_attachWith {p : α → Prop} {l : Array α} {H} : (l.attachWith p H).size = l.size := by
  cases l; simp

@[simp]
theorem pmap_eq_empty_iff {p : α → Prop} {f : ∀ a, p a → β} {l H} : pmap f l H = #[] ↔ l = #[] := by
  cases l; simp

theorem pmap_ne_empty_iff {P : α → Prop} (f : (a : α) → P a → β) {xs : Array α}
    (H : ∀ (a : α), a ∈ xs → P a) : xs.pmap f H ≠ #[] ↔ xs ≠ #[] := by
  cases xs; simp

theorem pmap_eq_self {l : Array α} {p : α → Prop} {hp : ∀ (a : α), a ∈ l → p a}
    {f : (a : α) → p a → α} : l.pmap f hp = l ↔ ∀ a (h : a ∈ l), f a (hp a h) = a := by
  cases l; simp [List.pmap_eq_self]

@[simp]
theorem attach_eq_empty_iff {l : Array α} : l.attach = #[] ↔ l = #[] := by
  cases l; simp

theorem attach_ne_empty_iff {l : Array α} : l.attach ≠ #[] ↔ l ≠ #[] := by
  cases l; simp

@[simp]
theorem attachWith_eq_empty_iff {l : Array α} {P : α → Prop} {H : ∀ a ∈ l, P a} :
    l.attachWith P H = #[] ↔ l = #[] := by
  cases l; simp

theorem attachWith_ne_empty_iff {l : Array α} {P : α → Prop} {H : ∀ a ∈ l, P a} :
    l.attachWith P H ≠ #[] ↔ l ≠ #[] := by
  cases l; simp

@[simp]
theorem getElem?_pmap {p : α → Prop} (f : ∀ a, p a → β) {l : Array α} (h : ∀ a ∈ l, p a) (i : Nat) :
    (pmap f l h)[i]? = Option.pmap f l[i]? fun x H => h x (mem_of_getElem? H) := by
  cases l; simp

@[simp]
theorem getElem_pmap {p : α → Prop} (f : ∀ a, p a → β) {l : Array α} (h : ∀ a ∈ l, p a) {i : Nat}
    (hi : i < (pmap f l h).size) :
    (pmap f l h)[i] =
      f (l[i]'(@size_pmap _ _ p f l h ▸ hi))
        (h _ (getElem_mem (@size_pmap _ _ p f l h ▸ hi))) := by
  cases l; simp

@[simp]
theorem getElem?_attachWith {xs : Array α} {i : Nat} {P : α → Prop} {H : ∀ a ∈ xs, P a} :
    (xs.attachWith P H)[i]? = xs[i]?.pmap Subtype.mk (fun _ a => H _ (mem_of_getElem? a)) :=
  getElem?_pmap ..

@[simp]
theorem getElem?_attach {xs : Array α} {i : Nat} :
    xs.attach[i]? = xs[i]?.pmap Subtype.mk (fun _ a => mem_of_getElem? a) :=
  getElem?_attachWith

@[simp]
theorem getElem_attachWith {xs : Array α} {P : α → Prop} {H : ∀ a ∈ xs, P a}
    {i : Nat} (h : i < (xs.attachWith P H).size) :
    (xs.attachWith P H)[i] = ⟨xs[i]'(by simpa using h), H _ (getElem_mem (by simpa using h))⟩ :=
  getElem_pmap _ _ h

@[simp]
theorem getElem_attach {xs : Array α} {i : Nat} (h : i < xs.attach.size) :
    xs.attach[i] = ⟨xs[i]'(by simpa using h), getElem_mem (by simpa using h)⟩ :=
  getElem_attachWith h

@[simp] theorem pmap_attach (l : Array α) {p : {x // x ∈ l} → Prop} (f : ∀ a, p a → β) (H) :
    pmap f l.attach H =
      l.pmap (P := fun a => ∃ h : a ∈ l, p ⟨a, h⟩)
        (fun a h => f ⟨a, h.1⟩ h.2) (fun a h => ⟨h, H ⟨a, h⟩ (by simp)⟩) := by
  ext <;> simp

@[simp] theorem pmap_attachWith (l : Array α) {p : {x // q x} → Prop} (f : ∀ a, p a → β) (H₁ H₂) :
    pmap f (l.attachWith q H₁) H₂ =
      l.pmap (P := fun a => ∃ h : q a, p ⟨a, h⟩)
        (fun a h => f ⟨a, h.1⟩ h.2) (fun a h => ⟨H₁ _ h, H₂ ⟨a, H₁ _ h⟩ (by simpa)⟩) := by
  ext <;> simp

theorem foldl_pmap (l : Array α) {P : α → Prop} (f : (a : α) → P a → β)
  (H : ∀ (a : α), a ∈ l → P a) (g : γ → β → γ) (x : γ) :
    (l.pmap f H).foldl g x = l.attach.foldl (fun acc a => g acc (f a.1 (H _ a.2))) x := by
  rw [pmap_eq_map_attach, foldl_map]

theorem foldr_pmap (l : Array α) {P : α → Prop} (f : (a : α) → P a → β)
  (H : ∀ (a : α), a ∈ l → P a) (g : β → γ → γ) (x : γ) :
    (l.pmap f H).foldr g x = l.attach.foldr (fun a acc => g (f a.1 (H _ a.2)) acc) x := by
  rw [pmap_eq_map_attach, foldr_map]

@[simp] theorem foldl_attachWith
    (l : Array α) {q : α → Prop} (H : ∀ a, a ∈ l → q a) {f : β → { x // q x} → β} {b} (w : stop = l.size) :
    (l.attachWith q H).foldl f b 0 stop = l.attach.foldl (fun b ⟨a, h⟩ => f b ⟨a, H _ h⟩) b := by
  subst w
  rcases l with ⟨l⟩
  simp [List.foldl_attachWith, List.foldl_map]

@[simp] theorem foldr_attachWith
    (l : Array α) {q : α → Prop} (H : ∀ a, a ∈ l → q a) {f : { x // q x} → β → β} {b} (w : start = l.size) :
    (l.attachWith q H).foldr f b start 0 = l.attach.foldr (fun a acc => f ⟨a.1, H _ a.2⟩ acc) b := by
  subst w
  rcases l with ⟨l⟩
  simp [List.foldr_attachWith, List.foldr_map]

/--
If we fold over `l.attach` with a function that ignores the membership predicate,
we get the same results as folding over `l` directly.

This is useful when we need to use `attach` to show termination.

Unfortunately this can't be applied by `simp` because of the higher order unification problem,
and even when rewriting we need to specify the function explicitly.
See however `foldl_subtype` below.
-/
theorem foldl_attach (l : Array α) (f : β → α → β) (b : β) :
    l.attach.foldl (fun acc t => f acc t.1) b = l.foldl f b := by
  rcases l with ⟨l⟩
  simp only [List.attach_toArray, List.attachWith_mem_toArray, size_toArray,
    List.length_pmap, List.foldl_toArray', mem_toArray, List.foldl_subtype]
  congr
  ext
  simpa using fun a => List.mem_of_getElem? a

/--
If we fold over `l.attach` with a function that ignores the membership predicate,
we get the same results as folding over `l` directly.

This is useful when we need to use `attach` to show termination.

Unfortunately this can't be applied by `simp` because of the higher order unification problem,
and even when rewriting we need to specify the function explicitly.
See however `foldr_subtype` below.
-/
theorem foldr_attach (l : Array α) (f : α → β → β) (b : β) :
    l.attach.foldr (fun t acc => f t.1 acc) b = l.foldr f b := by
  rcases l with ⟨l⟩
  simp only [List.attach_toArray, List.attachWith_mem_toArray, size_toArray,
    List.length_pmap, List.foldr_toArray', mem_toArray, List.foldr_subtype]
  congr
  ext
  simpa using fun a => List.mem_of_getElem? a

theorem attach_map {l : Array α} (f : α → β) :
    (l.map f).attach = l.attach.map (fun ⟨x, h⟩ => ⟨f x, mem_map_of_mem f h⟩) := by
  cases l
  ext <;> simp

theorem attachWith_map {l : Array α} (f : α → β) {P : β → Prop} {H : ∀ (b : β), b ∈ l.map f → P b} :
    (l.map f).attachWith P H = (l.attachWith (P ∘ f) (fun _ h => H _ (mem_map_of_mem f h))).map
      fun ⟨x, h⟩ => ⟨f x, h⟩ := by
  cases l
  simp [List.attachWith_map]

@[simp] theorem map_attachWith {l : Array α} {P : α → Prop} {H : ∀ (a : α), a ∈ l → P a}
    (f : { x // P x } → β) :
    (l.attachWith P H).map f = l.attach.map fun ⟨x, h⟩ => f ⟨x, H _ h⟩ := by
  cases l <;> simp_all

theorem map_attachWith_eq_pmap {l : Array α} {P : α → Prop} {H : ∀ (a : α), a ∈ l → P a}
    (f : { x // P x } → β) :
    (l.attachWith P H).map f =
      l.pmap (fun a (h : a ∈ l ∧ P a) => f ⟨a, H _ h.1⟩) (fun a h => ⟨h, H a h⟩) := by
  cases l
  ext <;> simp

/-- See also `pmap_eq_map_attach` for writing `pmap` in terms of `map` and `attach`. -/
theorem map_attach_eq_pmap {l : Array α} (f : { x // x ∈ l } → β) :
    l.attach.map f = l.pmap (fun a h => f ⟨a, h⟩) (fun _ => id) := by
  cases l
  ext <;> simp

@[deprecated map_attach_eq_pmap (since := "2025-02-09")]
abbrev map_attach := @map_attach_eq_pmap

theorem attach_filterMap {l : Array α} {f : α → Option β} :
    (l.filterMap f).attach = l.attach.filterMap
      fun ⟨x, h⟩ => (f x).pbind (fun b m => some ⟨b, mem_filterMap.mpr ⟨x, h, m⟩⟩) := by
  cases l
  rw [attach_congr (List.filterMap_toArray f _)]
  simp [List.attach_filterMap, List.map_filterMap, Function.comp_def]

theorem attach_filter {l : Array α} (p : α → Bool) :
    (l.filter p).attach = l.attach.filterMap
      fun x => if w : p x.1 then some ⟨x.1, mem_filter.mpr ⟨x.2, w⟩⟩ else none := by
  cases l
  rw [attach_congr (List.filter_toArray p _)]
  simp [List.attach_filter, List.map_filterMap, Function.comp_def]

-- We are still missing here `attachWith_filterMap` and `attachWith_filter`.

@[simp]
theorem filterMap_attachWith {q : α → Prop} {l : Array α} {f : {x // q x} → Option β} (H)
    (w : stop = (l.attachWith q H).size) :
    (l.attachWith q H).filterMap f 0 stop = l.attach.filterMap (fun ⟨x, h⟩ => f ⟨x, H _ h⟩) := by
  subst w
  cases l
  simp [Function.comp_def]

@[simp]
theorem filter_attachWith {q : α → Prop} {l : Array α} {p : {x // q x} → Bool} (H)
    (w : stop = (l.attachWith q H).size) :
    (l.attachWith q H).filter p 0 stop =
      (l.attach.filter (fun ⟨x, h⟩ => p ⟨x, H _ h⟩)).map (fun ⟨x, h⟩ => ⟨x, H _ h⟩) := by
  subst w
  cases l
  simp [Function.comp_def, List.filter_map]

theorem pmap_pmap {p : α → Prop} {q : β → Prop} (g : ∀ a, p a → β) (f : ∀ b, q b → γ) (l H₁ H₂) :
    pmap f (pmap g l H₁) H₂ =
      pmap (α := { x // x ∈ l }) (fun a h => f (g a h) (H₂ (g a h) (mem_pmap_of_mem a.2))) l.attach
        (fun a _ => H₁ a a.2) := by
  cases l
  simp [List.pmap_pmap, List.pmap_map]

@[simp] theorem pmap_append {p : ι → Prop} (f : ∀ a : ι, p a → α) (l₁ l₂ : Array ι)
    (h : ∀ a ∈ l₁ ++ l₂, p a) :
    (l₁ ++ l₂).pmap f h =
      (l₁.pmap f fun a ha => h a (mem_append_left l₂ ha)) ++
        l₂.pmap f fun a ha => h a (mem_append_right l₁ ha) := by
  cases l₁
  cases l₂
  simp

theorem pmap_append' {p : α → Prop} (f : ∀ a : α, p a → β) (l₁ l₂ : Array α)
    (h₁ : ∀ a ∈ l₁, p a) (h₂ : ∀ a ∈ l₂, p a) :
    ((l₁ ++ l₂).pmap f fun a ha => (mem_append.1 ha).elim (h₁ a) (h₂ a)) =
      l₁.pmap f h₁ ++ l₂.pmap f h₂ :=
  pmap_append f l₁ l₂ _

@[simp] theorem attach_append (xs ys : Array α) :
    (xs ++ ys).attach = xs.attach.map (fun ⟨x, h⟩ => ⟨x, mem_append_left ys h⟩) ++
      ys.attach.map fun ⟨x, h⟩ => ⟨x, mem_append_right xs h⟩ := by
  cases xs
  cases ys
  rw [attach_congr (List.append_toArray _ _)]
  simp [List.attach_append, Function.comp_def]

@[simp] theorem attachWith_append {P : α → Prop} {xs ys : Array α}
    {H : ∀ (a : α), a ∈ xs ++ ys → P a} :
    (xs ++ ys).attachWith P H = xs.attachWith P (fun a h => H a (mem_append_left ys h)) ++
      ys.attachWith P (fun a h => H a (mem_append_right xs h)) := by
  simp [attachWith, attach_append, map_pmap, pmap_append]

@[simp] theorem pmap_reverse {P : α → Prop} (f : (a : α) → P a → β) (xs : Array α)
    (H : ∀ (a : α), a ∈ xs.reverse → P a) :
    xs.reverse.pmap f H = (xs.pmap f (fun a h => H a (by simpa using h))).reverse := by
  induction xs <;> simp_all

theorem reverse_pmap {P : α → Prop} (f : (a : α) → P a → β) (xs : Array α)
    (H : ∀ (a : α), a ∈ xs → P a) :
    (xs.pmap f H).reverse = xs.reverse.pmap f (fun a h => H a (by simpa using h)) := by
  rw [pmap_reverse]

@[simp] theorem attachWith_reverse {P : α → Prop} {xs : Array α}
    {H : ∀ (a : α), a ∈ xs.reverse → P a} :
    xs.reverse.attachWith P H =
      (xs.attachWith P (fun a h => H a (by simpa using h))).reverse := by
  cases xs
  simp

theorem reverse_attachWith {P : α → Prop} {xs : Array α}
    {H : ∀ (a : α), a ∈ xs → P a} :
    (xs.attachWith P H).reverse = (xs.reverse.attachWith P (fun a h => H a (by simpa using h))) := by
  cases xs
  simp

@[simp] theorem attach_reverse (xs : Array α) :
    xs.reverse.attach = xs.attach.reverse.map fun ⟨x, h⟩ => ⟨x, by simpa using h⟩ := by
  cases xs
  rw [attach_congr (List.reverse_toArray _)]
  simp

theorem reverse_attach (xs : Array α) :
    xs.attach.reverse = xs.reverse.attach.map fun ⟨x, h⟩ => ⟨x, by simpa using h⟩ := by
  cases xs
  simp

@[simp] theorem back?_pmap {P : α → Prop} (f : (a : α) → P a → β) (xs : Array α)
    (H : ∀ (a : α), a ∈ xs → P a) :
    (xs.pmap f H).back? = xs.attach.back?.map fun ⟨a, m⟩ => f a (H a m) := by
  cases xs
  simp

@[simp] theorem back?_attachWith {P : α → Prop} {xs : Array α}
    {H : ∀ (a : α), a ∈ xs → P a} :
    (xs.attachWith P H).back? = xs.back?.pbind (fun a h => some ⟨a, H _ (mem_of_back? h)⟩) := by
  cases xs
  simp

@[simp]
theorem back?_attach {xs : Array α} :
    xs.attach.back? = xs.back?.pbind fun a h => some ⟨a, mem_of_back? h⟩ := by
  cases xs
  simp

@[simp]
theorem countP_attach (l : Array α) (p : α → Bool) :
    l.attach.countP (fun a : {x // x ∈ l} => p a) = l.countP p := by
  cases l
  simp [Function.comp_def]

@[simp]
theorem countP_attachWith {p : α → Prop} (l : Array α) (H : ∀ a ∈ l, p a) (q : α → Bool) :
    (l.attachWith p H).countP (fun a : {x // p x} => q a) = l.countP q := by
  cases l
  simp

@[simp]
theorem count_attach [DecidableEq α] (l : Array α) (a : {x // x ∈ l}) :
    l.attach.count a = l.count ↑a := by
  rcases l with ⟨l⟩
  simp only [List.attach_toArray, List.attachWith_mem_toArray, List.count_toArray]
  rw [List.map_attach_eq_pmap, List.count_eq_countP]
  simp only [Subtype.beq_iff]
  rw [List.countP_pmap, List.countP_attach (p := (fun x => x == a.1)), List.count]

@[simp]
theorem count_attachWith [DecidableEq α] {p : α → Prop} (l : Array α) (H : ∀ a ∈ l, p a) (a : {x // p x}) :
    (l.attachWith p H).count a = l.count ↑a := by
  cases l
  simp

@[simp] theorem countP_pmap {p : α → Prop} (g : ∀ a, p a → β) (f : β → Bool) (l : Array α) (H₁) :
    (l.pmap g H₁).countP f =
      l.attach.countP (fun ⟨a, m⟩ => f (g a (H₁ a m))) := by
  simp [pmap_eq_map_attach, countP_map, Function.comp_def]

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
def unattach {α : Type _} {p : α → Prop} (l : Array { x // p x }) : Array α := l.map (·.val)

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
  simp only [List.attach_toArray, List.unattach_toArray, List.unattach_attachWith]

@[simp] theorem unattach_attachWith {p : α → Prop} {l : Array α}
    {H : ∀ a ∈ l, p a} :
    (l.attachWith p H).unattach = l := by
  cases l
  simp

@[simp] theorem getElem?_unattach {p : α → Prop} {l : Array { x // p x }} (i : Nat) :
    l.unattach[i]? = l[i]?.map Subtype.val := by
  simp [unattach]

@[simp] theorem getElem_unattach
    {p : α → Prop} {l : Array { x // p x }} (i : Nat) (h : i < l.unattach.size) :
    l.unattach[i] = (l[i]'(by simpa using h)).1 := by
  simp [unattach]

/-! ### Recognizing higher order functions using a function that only depends on the value. -/

/--
This lemma identifies folds over arrays of subtypes, where the function only depends on the value, not the proposition,
and simplifies these to the function directly taking the value.
-/
theorem foldl_subtype {p : α → Prop} {l : Array { x // p x }}
    {f : β → { x // p x } → β} {g : β → α → β} {x : β}
    (hf : ∀ b x h, f b ⟨x, h⟩ = g b x) :
    l.foldl f x = l.unattach.foldl g x := by
  cases l
  simp only [List.foldl_toArray', List.unattach_toArray]
  rw [List.foldl_subtype] -- Why can't simp do this?
  simp [hf]

/-- Variant of `foldl_subtype` with side condition to check `stop = l.size`. -/
@[simp] theorem foldl_subtype' {p : α → Prop} {l : Array { x // p x }}
    {f : β → { x // p x } → β} {g : β → α → β} {x : β}
    (hf : ∀ b x h, f b ⟨x, h⟩ = g b x) (h : stop = l.size) :
    l.foldl f x 0 stop = l.unattach.foldl g x := by
  subst h
  rwa [foldl_subtype]

/--
This lemma identifies folds over arrays of subtypes, where the function only depends on the value, not the proposition,
and simplifies these to the function directly taking the value.
-/
theorem foldr_subtype {p : α → Prop} {l : Array { x // p x }}
    {f : { x // p x } → β → β} {g : α → β → β} {x : β}
    (hf : ∀ x h b, f ⟨x, h⟩ b = g x b) :
    l.foldr f x = l.unattach.foldr g x := by
  cases l
  simp only [List.foldr_toArray', List.unattach_toArray]
  rw [List.foldr_subtype]
  simp [hf]

/-- Variant of `foldr_subtype` with side condition to check `stop = l.size`. -/
@[simp] theorem foldr_subtype' {p : α → Prop} {l : Array { x // p x }}
    {f : { x // p x } → β → β} {g : α → β → β} {x : β}
    (hf : ∀ x h b, f ⟨x, h⟩ b = g x b) (h : start = l.size) :
    l.foldr f x start 0 = l.unattach.foldr g x := by
  subst h
  rwa [foldr_subtype]

/--
This lemma identifies maps over arrays of subtypes, where the function only depends on the value, not the proposition,
and simplifies these to the function directly taking the value.
-/
@[simp] theorem map_subtype {p : α → Prop} {l : Array { x // p x }}
    {f : { x // p x } → β} {g : α → β} (hf : ∀ x h, f ⟨x, h⟩ = g x) :
    l.map f = l.unattach.map g := by
  cases l
  simp only [List.map_toArray, List.unattach_toArray]
  rw [List.map_subtype]
  simp [hf]

@[simp] theorem filterMap_subtype {p : α → Prop} {l : Array { x // p x }}
    {f : { x // p x } → Option β} {g : α → Option β} (hf : ∀ x h, f ⟨x, h⟩ = g x) :
    l.filterMap f = l.unattach.filterMap g := by
  cases l
  simp only [size_toArray, List.filterMap_toArray', List.unattach_toArray, List.length_unattach,
    mk.injEq]
  rw [List.filterMap_subtype]
  simp [hf]

@[simp] theorem findSome?_subtype {p : α → Prop} {l : Array { x // p x }}
    {f : { x // p x } → Option β} {g : α → Option β} (hf : ∀ x h, f ⟨x, h⟩ = g x) :
    l.findSome? f = l.unattach.findSome? g := by
  cases l
  simp
  rw [List.findSome?_subtype hf]

@[simp] theorem find?_subtype {p : α → Prop} {l : Array { x // p x }}
    {f : { x // p x } → Bool} {g : α → Bool} (hf : ∀ x h, f ⟨x, h⟩ = g x) :
    (l.find? f).map Subtype.val = l.unattach.find? g := by
  cases l
  simp
  rw [List.find?_subtype hf]

/-! ### Simp lemmas pushing `unattach` inwards. -/

@[simp] theorem unattach_filter {p : α → Prop} {l : Array { x // p x }}
    {f : { x // p x } → Bool} {g : α → Bool} (hf : ∀ x h, f ⟨x, h⟩ = g x) :
    (l.filter f).unattach = l.unattach.filter g := by
  cases l
  simp [hf]

@[simp] theorem unattach_reverse {p : α → Prop} {l : Array { x // p x }} :
    l.reverse.unattach = l.unattach.reverse := by
  cases l
  simp

@[simp] theorem unattach_append {p : α → Prop} {l₁ l₂ : Array { x // p x }} :
    (l₁ ++ l₂).unattach = l₁.unattach ++ l₂.unattach := by
  cases l₁
  cases l₂
  simp

@[simp] theorem unattach_flatten {p : α → Prop} {l : Array (Array { x // p x })} :
    l.flatten.unattach = (l.map unattach).flatten := by
  unfold unattach
  cases l using array₂_induction
  simp only [flatten_toArray, List.map_map, Function.comp_def, List.map_id_fun', id_eq,
    List.map_toArray, List.map_flatten, map_subtype, map_id_fun', List.unattach_toArray, mk.injEq]
  simp only [List.unattach]

@[simp] theorem unattach_mkArray {p : α → Prop} {n : Nat} {x : { x // p x }} :
    (Array.mkArray n x).unattach = Array.mkArray n x.1 := by
  simp [unattach]

end Array

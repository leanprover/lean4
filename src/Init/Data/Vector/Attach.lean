/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
prelude
import Init.Data.Vector.Lemmas
import Init.Data.Array.Attach

namespace Vector

/--
`O(n)`. Partial map. If `f : Π a, P a → β` is a partial function defined on
`a : α` satisfying `P`, then `pmap f l h` is essentially the same as `map f l`
but is defined only when all members of `l` satisfy `P`, using the proof
to apply `f`.

We replace this at runtime with a more efficient version via the `csimp` lemma `pmap_eq_pmapImpl`.
-/
def pmap {P : α → Prop} (f : ∀ a, P a → β) (l : Vector α n) (H : ∀ a ∈ l, P a) : Vector β n :=
  Vector.mk (l.toArray.pmap f (fun a m => H a (by simpa using m))) (by simp)

/--
Unsafe implementation of `attachWith`, taking advantage of the fact that the representation of
`Vector {x // P x} n` is the same as the input `Vector α n`.
-/
@[inline] private unsafe def attachWithImpl
    (xs : Vector α n) (P : α → Prop) (_ : ∀ x ∈ xs, P x) : Vector {x // P x} n := unsafeCast xs

/-- `O(1)`. "Attach" a proof `P x` that holds for all the elements of `xs` to produce a new array
  with the same elements but in the type `{x // P x}`. -/
@[implemented_by attachWithImpl] def attachWith
    (xs : Vector α n) (P : α → Prop) (H : ∀ x ∈ xs, P x) : Vector {x // P x} n :=
  Vector.mk (xs.toArray.attachWith P fun x h => H x (by simpa using h)) (by simp)

/-- `O(1)`. "Attach" the proof that the elements of `xs` are in `xs` to produce a new vector
  with the same elements but in the type `{x // x ∈ xs}`. -/
@[inline] def attach (xs : Vector α n) : Vector {x // x ∈ xs} n := xs.attachWith _ fun _ => id

@[simp] theorem attachWith_mk {xs : Array α} {h : xs.size = n} {P : α → Prop} {H : ∀ x ∈ mk xs h, P x} :
    (mk xs h).attachWith P H = mk (xs.attachWith P (by simpa using H)) (by simpa using h) := by
  simp [attachWith]

@[simp] theorem attach_mk {xs : Array α} {h : xs.size = n} :
    (mk xs h).attach = mk (xs.attachWith (· ∈ mk xs h) (by simp)) (by simpa using h):= by
  simp [attach]

@[simp] theorem pmap_mk {xs : Array α} {h : xs.size = n} {P : α → Prop} {f : ∀ a, P a → β}
    {H : ∀ a ∈ mk xs h, P a} :
    (mk xs h).pmap f H = mk (xs.pmap f (by simpa using H)) (by simpa using h) := by
  simp [pmap]

@[simp] theorem toArray_attachWith {l : Vector α n} {P : α → Prop} {H : ∀ x ∈ l, P x} :
   (l.attachWith P H).toArray = l.toArray.attachWith P (by simpa using H) := by
  simp [attachWith]

@[simp] theorem toArray_attach {α : Type _} {l : Vector α n} :
    l.attach.toArray = l.toArray.attachWith (· ∈ l) (by simp) := by
  simp [attach]

@[simp] theorem toArray_pmap {l : Vector α n} {P : α → Prop} {f : ∀ a, P a → β} {H : ∀ a ∈ l, P a} :
    (l.pmap f H).toArray = l.toArray.pmap f (fun a m => H a (by simpa using m)) := by
  simp [pmap]

@[simp] theorem toList_attachWith {l : Vector α n} {P : α → Prop} {H : ∀ x ∈ l, P x} :
   (l.attachWith P H).toList = l.toList.attachWith P (by simpa using H) := by
  simp [attachWith]

@[simp] theorem toList_attach {α : Type _} {l : Vector α n} :
    l.attach.toList = l.toList.attachWith (· ∈ l) (by simp) := by
  simp [attach]

@[simp] theorem toList_pmap {l : Vector α n} {P : α → Prop} {f : ∀ a, P a → β} {H : ∀ a ∈ l, P a} :
    (l.pmap f H).toList = l.toList.pmap f (fun a m => H a (by simpa using m)) := by
  simp [pmap]

/-- Implementation of `pmap` using the zero-copy version of `attach`. -/
@[inline] private def pmapImpl {P : α → Prop} (f : ∀ a, P a → β) (l : Vector α n) (H : ∀ a ∈ l, P a) :
    Vector β n := (l.attachWith _ H).map fun ⟨x, h'⟩ => f x h'

@[csimp] private theorem pmap_eq_pmapImpl : @pmap = @pmapImpl := by
  funext α β n p f L h'
  rcases L with ⟨L, rfl⟩
  simp only [pmap, pmapImpl, attachWith_mk, map_mk, Array.map_attachWith_eq_pmap, eq_mk]
  apply Array.pmap_congr_left
  intro a m h₁ h₂
  congr

@[simp] theorem pmap_empty {P : α → Prop} (f : ∀ a, P a → β) : pmap f #v[] (by simp) = #v[] := rfl

@[simp] theorem pmap_push {P : α → Prop} (f : ∀ a, P a → β) (a : α) (l : Vector α n) (h : ∀ b ∈ l.push a, P b) :
    pmap f (l.push a) h =
      (pmap f l (fun a m => by simp at h; exact h a (.inl m))).push (f a (h a (by simp))) := by
  simp [pmap]

@[simp] theorem attach_empty : (#v[] : Vector α 0).attach = #v[] := rfl

@[simp] theorem attachWith_empty {P : α → Prop} (H : ∀ x ∈ #v[], P x) : (#v[] : Vector α 0).attachWith P H = #v[] := rfl

@[simp]
theorem pmap_eq_map (p : α → Prop) (f : α → β) (l : Vector α n) (H) :
    @pmap _ _ _ p (fun a _ => f a) l H = map f l := by
  cases l; simp

theorem pmap_congr_left {p q : α → Prop} {f : ∀ a, p a → β} {g : ∀ a, q a → β} (l : Vector α n) {H₁ H₂}
    (h : ∀ a ∈ l, ∀ (h₁ h₂), f a h₁ = g a h₂) : pmap f l H₁ = pmap g l H₂ := by
  rcases l with ⟨l, rfl⟩
  simp only [pmap_mk, eq_mk]
  apply Array.pmap_congr_left
  simpa using h

theorem map_pmap {p : α → Prop} (g : β → γ) (f : ∀ a, p a → β) (l : Vector α n) (H) :
    map g (pmap f l H) = pmap (fun a h => g (f a h)) l H := by
  rcases l with ⟨l, rfl⟩
  simp [Array.map_pmap]

theorem pmap_map {p : β → Prop} (g : ∀ b, p b → γ) (f : α → β) (l : Vector α n) (H) :
    pmap g (map f l) H = pmap (fun a h => g (f a) h) l fun _ h => H _ (mem_map_of_mem _ h) := by
  rcases l with ⟨l, rfl⟩
  simp [Array.pmap_map]

theorem attach_congr {l₁ l₂ : Vector α n} (h : l₁ = l₂) :
    l₁.attach = l₂.attach.map (fun x => ⟨x.1, h ▸ x.2⟩) := by
  subst h
  simp

theorem attachWith_congr {l₁ l₂ : Vector α n} (w : l₁ = l₂) {P : α → Prop} {H : ∀ x ∈ l₁, P x} :
    l₁.attachWith P H = l₂.attachWith P fun _ h => H _ (w ▸ h) := by
  subst w
  simp

@[simp] theorem attach_push {a : α} {l : Vector α n} :
    (l.push a).attach =
      (l.attach.map (fun ⟨x, h⟩ => ⟨x, mem_push_of_mem a h⟩)).push ⟨a, by simp⟩ := by
  rcases l with ⟨l, rfl⟩
  simp [Array.map_attach_eq_pmap]

@[simp] theorem attachWith_push {a : α} {l : Vector α n} {P : α → Prop} {H : ∀ x ∈ l.push a, P x} :
    (l.push a).attachWith P H =
      (l.attachWith P (fun x h => by simp at H; exact H x (.inl h))).push ⟨a, H a (by simp)⟩ := by
  rcases l with ⟨l, rfl⟩
  simp

theorem pmap_eq_map_attach {p : α → Prop} (f : ∀ a, p a → β) (l : Vector α n) (H) :
    pmap f l H = l.attach.map fun x => f x.1 (H _ x.2) := by
  rcases l with ⟨l, rfl⟩
  simp only [pmap_mk, Array.pmap_eq_map_attach, attach_mk, map_mk, eq_mk]
  rw [Array.map_attach_eq_pmap, Array.map_attachWith]
  ext i hi₁ hi₂ <;> simp

@[simp]
theorem pmap_eq_attachWith {p q : α → Prop} (f : ∀ a, p a → q a) (l : Vector α n) (H) :
    pmap (fun a h => ⟨a, f a h⟩) l H = l.attachWith q (fun x h => f x (H x h)) := by
  cases l
  simp

theorem attach_map_coe (l : Vector α n) (f : α → β) :
    (l.attach.map fun (i : {i // i ∈ l}) => f i) = l.map f := by
  cases l
  simp

theorem attach_map_val (l : Vector α n) (f : α → β) : (l.attach.map fun i => f i.val) = l.map f :=
  attach_map_coe _ _

theorem attach_map_subtype_val (l : Vector α n) : l.attach.map Subtype.val = l := by
  cases l; simp

theorem attachWith_map_coe {p : α → Prop} (f : α → β) (l : Vector α n) (H : ∀ a ∈ l, p a) :
    ((l.attachWith p H).map fun (i : { i // p i}) => f i) = l.map f := by
  cases l; simp

theorem attachWith_map_val {p : α → Prop} (f : α → β) (l : Vector α n) (H : ∀ a ∈ l, p a) :
    ((l.attachWith p H).map fun i => f i.val) = l.map f :=
  attachWith_map_coe _ _ _

theorem attachWith_map_subtype_val {p : α → Prop} (l : Vector α n) (H : ∀ a ∈ l, p a) :
    (l.attachWith p H).map Subtype.val = l := by
  cases l; simp

@[simp]
theorem mem_attach (l : Vector α n) : ∀ x, x ∈ l.attach
  | ⟨a, h⟩ => by
    have := mem_map.1 (by rw [attach_map_subtype_val] <;> exact h)
    rcases this with ⟨⟨_, _⟩, m, rfl⟩
    exact m

@[simp]
theorem mem_attachWith (l : Vector α n) {q : α → Prop} (H) (x : {x // q x}) :
    x ∈ l.attachWith q H ↔ x.1 ∈ l := by
  rcases l with ⟨l, rfl⟩
  simp

@[simp]
theorem mem_pmap {p : α → Prop} {f : ∀ a, p a → β} {l : Vector α n} {H b} :
    b ∈ pmap f l H ↔ ∃ (a : _) (h : a ∈ l), f a (H a h) = b := by
  simp only [pmap_eq_map_attach, mem_map, mem_attach, true_and, Subtype.exists, eq_comm]

theorem mem_pmap_of_mem {p : α → Prop} {f : ∀ a, p a → β} {l : Vector α n} {H} {a} (h : a ∈ l) :
    f a (H a h) ∈ pmap f l H := by
  rw [mem_pmap]
  exact ⟨a, h, rfl⟩

theorem pmap_eq_self {l : Vector α n} {p : α → Prop} {hp : ∀ (a : α), a ∈ l → p a}
    {f : (a : α) → p a → α} : l.pmap f hp = l ↔ ∀ a (h : a ∈ l), f a (hp a h) = a := by
  cases l; simp [Array.pmap_eq_self]

@[simp]
theorem getElem?_pmap {p : α → Prop} (f : ∀ a, p a → β) {l : Vector α n} (h : ∀ a ∈ l, p a) (i : Nat) :
    (pmap f l h)[i]? = Option.pmap f l[i]? fun x H => h x (mem_of_getElem? H) := by
  cases l; simp

@[simp]
theorem getElem_pmap {p : α → Prop} (f : ∀ a, p a → β) {l : Vector α n} (h : ∀ a ∈ l, p a) {i : Nat}
    (hn : i < n) :
    (pmap f l h)[i] = f (l[i]) (h _ (by simp)) := by
  cases l; simp

@[simp]
theorem getElem?_attachWith {xs : Vector α n} {i : Nat} {P : α → Prop} {H : ∀ a ∈ xs, P a} :
    (xs.attachWith P H)[i]? = xs[i]?.pmap Subtype.mk (fun _ a => H _ (mem_of_getElem? a)) :=
  getElem?_pmap ..

@[simp]
theorem getElem?_attach {xs : Vector α n} {i : Nat} :
    xs.attach[i]? = xs[i]?.pmap Subtype.mk (fun _ a => mem_of_getElem? a) :=
  getElem?_attachWith

@[simp]
theorem getElem_attachWith {xs : Vector α n} {P : α → Prop} {H : ∀ a ∈ xs, P a}
    {i : Nat} (h : i < n) :
    (xs.attachWith P H)[i] = ⟨xs[i]'(by simpa using h), H _ (getElem_mem (by simpa using h))⟩ :=
  getElem_pmap _ _ h

@[simp]
theorem getElem_attach {xs : Vector α n} {i : Nat} (h : i < n) :
    xs.attach[i] = ⟨xs[i]'(by simpa using h), getElem_mem (by simpa using h)⟩ :=
  getElem_attachWith h

@[simp] theorem pmap_attach (l : Vector α n) {p : {x // x ∈ l} → Prop} (f : ∀ a, p a → β) (H) :
    pmap f l.attach H =
      l.pmap (P := fun a => ∃ h : a ∈ l, p ⟨a, h⟩)
        (fun a h => f ⟨a, h.1⟩ h.2) (fun a h => ⟨h, H ⟨a, h⟩ (by simp)⟩) := by
  ext <;> simp

@[simp] theorem pmap_attachWith (l : Vector α n) {p : {x // q x} → Prop} (f : ∀ a, p a → β) (H₁ H₂) :
    pmap f (l.attachWith q H₁) H₂ =
      l.pmap (P := fun a => ∃ h : q a, p ⟨a, h⟩)
        (fun a h => f ⟨a, h.1⟩ h.2) (fun a h => ⟨H₁ _ h, H₂ ⟨a, H₁ _ h⟩ (by simpa)⟩) := by
  ext <;> simp

theorem foldl_pmap (l : Vector α n) {P : α → Prop} (f : (a : α) → P a → β)
  (H : ∀ (a : α), a ∈ l → P a) (g : γ → β → γ) (x : γ) :
    (l.pmap f H).foldl g x = l.attach.foldl (fun acc a => g acc (f a.1 (H _ a.2))) x := by
  rw [pmap_eq_map_attach, foldl_map]

theorem foldr_pmap (l : Vector α n) {P : α → Prop} (f : (a : α) → P a → β)
  (H : ∀ (a : α), a ∈ l → P a) (g : β → γ → γ) (x : γ) :
    (l.pmap f H).foldr g x = l.attach.foldr (fun a acc => g (f a.1 (H _ a.2)) acc) x := by
  rw [pmap_eq_map_attach, foldr_map]

/--
If we fold over `l.attach` with a function that ignores the membership predicate,
we get the same results as folding over `l` directly.

This is useful when we need to use `attach` to show termination.

Unfortunately this can't be applied by `simp` because of the higher order unification problem,
and even when rewriting we need to specify the function explicitly.
See however `foldl_subtype` below.
-/
theorem foldl_attach (l : Vector α n) (f : β → α → β) (b : β) :
    l.attach.foldl (fun acc t => f acc t.1) b = l.foldl f b := by
  rcases l with ⟨l, rfl⟩
  simp [Array.foldl_attach]

/--
If we fold over `l.attach` with a function that ignores the membership predicate,
we get the same results as folding over `l` directly.

This is useful when we need to use `attach` to show termination.

Unfortunately this can't be applied by `simp` because of the higher order unification problem,
and even when rewriting we need to specify the function explicitly.
See however `foldr_subtype` below.
-/
theorem foldr_attach (l : Vector α n) (f : α → β → β) (b : β) :
    l.attach.foldr (fun t acc => f t.1 acc) b = l.foldr f b := by
  rcases l with ⟨l, rfl⟩
  simp [Array.foldr_attach]

theorem attach_map {l : Vector α n} (f : α → β) :
    (l.map f).attach = l.attach.map (fun ⟨x, h⟩ => ⟨f x, mem_map_of_mem f h⟩) := by
  cases l
  ext <;> simp

theorem attachWith_map {l : Vector α n} (f : α → β) {P : β → Prop} {H : ∀ (b : β), b ∈ l.map f → P b} :
    (l.map f).attachWith P H = (l.attachWith (P ∘ f) (fun _ h => H _ (mem_map_of_mem f h))).map
      fun ⟨x, h⟩ => ⟨f x, h⟩ := by
  rcases l with ⟨l, rfl⟩
  simp [Array.attachWith_map]

@[simp] theorem map_attachWith {l : Vector α n} {P : α → Prop} {H : ∀ (a : α), a ∈ l → P a}
    (f : { x // P x } → β) :
    (l.attachWith P H).map f = l.attach.map fun ⟨x, h⟩ => f ⟨x, H _ h⟩ := by
  rcases l with ⟨l, rfl⟩
  simp [Array.map_attachWith]

theorem map_attachWith_eq_pmap {l : Vector α n} {P : α → Prop} {H : ∀ (a : α), a ∈ l → P a}
    (f : { x // P x } → β) :
    (l.attachWith P H).map f =
      l.pmap (fun a (h : a ∈ l ∧ P a) => f ⟨a, H _ h.1⟩) (fun a h => ⟨h, H a h⟩) := by
  cases l
  ext <;> simp

/-- See also `pmap_eq_map_attach` for writing `pmap` in terms of `map` and `attach`. -/
theorem map_attach_eq_pmap {l : Vector α n} (f : { x // x ∈ l } → β) :
    l.attach.map f = l.pmap (fun a h => f ⟨a, h⟩) (fun _ => id) := by
  cases l
  ext <;> simp

@[deprecated map_attach_eq_pmap (since := "2025-02-09")]
abbrev map_attach := @map_attach_eq_pmap

theorem pmap_pmap {p : α → Prop} {q : β → Prop} (g : ∀ a, p a → β) (f : ∀ b, q b → γ) (l : Vector α n) (H₁ H₂) :
    pmap f (pmap g l H₁) H₂ =
      pmap (α := { x // x ∈ l }) (fun a h => f (g a h) (H₂ (g a h) (mem_pmap_of_mem a.2))) l.attach
        (fun a _ => H₁ a a.2) := by
  rcases l with ⟨l, rfl⟩
  ext <;> simp

@[simp] theorem pmap_append {p : ι → Prop} (f : ∀ a : ι, p a → α) (l₁ : Vector ι n) (l₂ : Vector ι m)
    (h : ∀ a ∈ l₁ ++ l₂, p a) :
    (l₁ ++ l₂).pmap f h =
      (l₁.pmap f fun a ha => h a (mem_append_left l₂ ha)) ++
        l₂.pmap f fun a ha => h a (mem_append_right l₁ ha) := by
  cases l₁
  cases l₂
  simp

theorem pmap_append' {p : α → Prop} (f : ∀ a : α, p a → β) (l₁ : Vector α n) (l₂ : Vector α m)
    (h₁ : ∀ a ∈ l₁, p a) (h₂ : ∀ a ∈ l₂, p a) :
    ((l₁ ++ l₂).pmap f fun a ha => (mem_append.1 ha).elim (h₁ a) (h₂ a)) =
      l₁.pmap f h₁ ++ l₂.pmap f h₂ :=
  pmap_append f l₁ l₂ _

@[simp] theorem attach_append (xs : Vector α n) (ys : Vector α m) :
    (xs ++ ys).attach = xs.attach.map (fun ⟨x, h⟩ => (⟨x, mem_append_left ys h⟩ : { x // x ∈ xs ++ ys })) ++
      ys.attach.map (fun ⟨y, h⟩ => (⟨y, mem_append_right xs h⟩ : { y // y ∈ xs ++ ys })) := by
  rcases xs with ⟨xs, rfl⟩
  rcases ys with ⟨ys, rfl⟩
  simp [Array.map_attach_eq_pmap]

@[simp] theorem attachWith_append {P : α → Prop} {xs : Vector α n} {ys : Vector α m}
    {H : ∀ (a : α), a ∈ xs ++ ys → P a} :
    (xs ++ ys).attachWith P H = xs.attachWith P (fun a h => H a (mem_append_left ys h)) ++
      ys.attachWith P (fun a h => H a (mem_append_right xs h)) := by
  simp [attachWith, attach_append, map_pmap, pmap_append]

@[simp] theorem pmap_reverse {P : α → Prop} (f : (a : α) → P a → β) (xs : Vector α n)
    (H : ∀ (a : α), a ∈ xs.reverse → P a) :
    xs.reverse.pmap f H = (xs.pmap f (fun a h => H a (by simpa using h))).reverse := by
  induction xs <;> simp_all

theorem reverse_pmap {P : α → Prop} (f : (a : α) → P a → β) (xs : Vector α n)
    (H : ∀ (a : α), a ∈ xs → P a) :
    (xs.pmap f H).reverse = xs.reverse.pmap f (fun a h => H a (by simpa using h)) := by
  rw [pmap_reverse]

@[simp] theorem attachWith_reverse {P : α → Prop} {xs : Vector α n}
    {H : ∀ (a : α), a ∈ xs.reverse → P a} :
    xs.reverse.attachWith P H =
      (xs.attachWith P (fun a h => H a (by simpa using h))).reverse := by
  cases xs
  simp

theorem reverse_attachWith {P : α → Prop} {xs : Vector α n}
    {H : ∀ (a : α), a ∈ xs → P a} :
    (xs.attachWith P H).reverse = (xs.reverse.attachWith P (fun a h => H a (by simpa using h))) := by
  cases xs
  simp

@[simp] theorem attach_reverse (xs : Vector α n) :
    xs.reverse.attach = xs.attach.reverse.map fun ⟨x, h⟩ => ⟨x, by simpa using h⟩ := by
  cases xs
  rw [attach_congr (reverse_mk ..)]
  simp [Array.map_attachWith]

theorem reverse_attach (xs : Vector α n) :
    xs.attach.reverse = xs.reverse.attach.map fun ⟨x, h⟩ => ⟨x, by simpa using h⟩ := by
  cases xs
  simp [Array.map_attach_eq_pmap]

@[simp] theorem back?_pmap {P : α → Prop} (f : (a : α) → P a → β) (xs : Vector α n)
    (H : ∀ (a : α), a ∈ xs → P a) :
    (xs.pmap f H).back? = xs.attach.back?.map fun ⟨a, m⟩ => f a (H a m) := by
  cases xs
  simp

@[simp] theorem back?_attachWith {P : α → Prop} {xs : Vector α n}
    {H : ∀ (a : α), a ∈ xs → P a} :
    (xs.attachWith P H).back? = xs.back?.pbind (fun a h => some ⟨a, H _ (mem_of_back? h)⟩) := by
  cases xs
  simp

@[simp]
theorem back?_attach {xs : Vector α n} :
    xs.attach.back? = xs.back?.pbind fun a h => some ⟨a, mem_of_back? h⟩ := by
  cases xs
  simp

@[simp]
theorem countP_attach (l : Vector α n) (p : α → Bool) :
    l.attach.countP (fun a : {x // x ∈ l} => p a) = l.countP p := by
  cases l
  simp [Function.comp_def]

@[simp]
theorem countP_attachWith {p : α → Prop} (l : Vector α n) (H : ∀ a ∈ l, p a) (q : α → Bool) :
    (l.attachWith p H).countP (fun a : {x // p x} => q a) = l.countP q := by
  cases l
  simp

@[simp]
theorem count_attach [DecidableEq α] (l : Vector α n) (a : {x // x ∈ l}) :
    l.attach.count a = l.count ↑a := by
  rcases l with ⟨l, rfl⟩
  simp

@[simp]
theorem count_attachWith [DecidableEq α] {p : α → Prop} (l : Vector α n) (H : ∀ a ∈ l, p a) (a : {x // p x}) :
    (l.attachWith p H).count a = l.count ↑a := by
  cases l
  simp

@[simp] theorem countP_pmap {p : α → Prop} (g : ∀ a, p a → β) (f : β → Bool) (l : Vector α n) (H₁) :
    (l.pmap g H₁).countP f =
      l.attach.countP (fun ⟨a, m⟩ => f (g a (H₁ a m))) := by
  rcases l with ⟨l, rfl⟩
  simp only [pmap_mk, countP_mk, Array.countP_pmap]
  simp [Array.countP_eq_size_filter]

/-! ## unattach

`Vector.unattach` is the (one-sided) inverse of `Vector.attach`. It is a synonym for `Vector.map Subtype.val`.

We use it by providing a simp lemma `l.attach.unattach = l`, and simp lemmas which recognize higher order
functions applied to `l : Vector { x // p x }` which only depend on the value, not the predicate, and rewrite these
in terms of a simpler function applied to `l.unattach`.

Further, we provide simp lemmas that push `unattach` inwards.
-/

/--
A synonym for `l.map (·.val)`. Mostly this should not be needed by users.
It is introduced as in intermediate step by lemmas such as `map_subtype`,
and is ideally subsequently simplified away by `unattach_attach`.

If not, usually the right approach is `simp [Vector.unattach, -Vector.map_subtype]` to unfold.
-/
def unattach {α : Type _} {p : α → Prop} (l : Vector { x // p x } n) : Vector α n := l.map (·.val)

@[simp] theorem unattach_nil {p : α → Prop} : (#v[] : Vector { x // p x } 0).unattach = #v[] := rfl
@[simp] theorem unattach_push {p : α → Prop} {a : { x // p x }} {l : Vector { x // p x } n} :
    (l.push a).unattach = l.unattach.push a.1 := by
  simp only [unattach, Vector.map_push]

@[simp] theorem unattach_mk {p : α → Prop} {l : Array { x // p x }} {h : l.size = n} :
    (mk l h).unattach = mk l.unattach (by simpa using h) := by
  simp [unattach]

@[simp] theorem toArray_unattach {p : α → Prop} {l : Vector { x // p x } n} :
    l.unattach.toArray = l.toArray.unattach := by
  simp [unattach]

@[simp] theorem toList_unattach {p : α → Prop} {l : Array { x // p x }} :
    l.unattach.toList = l.toList.unattach := by
  simp [unattach]

@[simp] theorem unattach_attach {l : Vector α n} : l.attach.unattach = l := by
  rcases l with ⟨l, rfl⟩
  simp

@[simp] theorem unattach_attachWith {p : α → Prop} {l : Vector α n}
    {H : ∀ a ∈ l, p a} :
    (l.attachWith p H).unattach = l := by
  cases l
  simp

@[simp] theorem getElem?_unattach {p : α → Prop} {l : Vector { x // p x } n} (i : Nat) :
    l.unattach[i]? = l[i]?.map Subtype.val := by
  simp [unattach]

@[simp] theorem getElem_unattach
    {p : α → Prop} {l : Vector { x // p x } n} (i : Nat) (h : i < n) :
    l.unattach[i] = (l[i]'(by simpa using h)).1 := by
  simp [unattach]

/-! ### Recognizing higher order functions using a function that only depends on the value. -/

/--
This lemma identifies folds over arrays of subtypes, where the function only depends on the value, not the proposition,
and simplifies these to the function directly taking the value.
-/
@[simp] theorem foldl_subtype {p : α → Prop} {l : Vector { x // p x } n}
    {f : β → { x // p x } → β} {g : β → α → β} {x : β}
    (hf : ∀ b x h, f b ⟨x, h⟩ = g b x) :
    l.foldl f x = l.unattach.foldl g x := by
  rcases l with ⟨l, rfl⟩
  simp [Array.foldl_subtype hf]

/--
This lemma identifies folds over arrays of subtypes, where the function only depends on the value, not the proposition,
and simplifies these to the function directly taking the value.
-/
@[simp] theorem foldr_subtype {p : α → Prop} {l : Vector { x // p x } n}
    {f : { x // p x } → β → β} {g : α → β → β} {x : β}
    (hf : ∀ x h b, f ⟨x, h⟩ b = g x b) :
    l.foldr f x = l.unattach.foldr g x := by
  rcases l with ⟨l, rfl⟩
  simp [Array.foldr_subtype hf]

/--
This lemma identifies maps over arrays of subtypes, where the function only depends on the value, not the proposition,
and simplifies these to the function directly taking the value.
-/
@[simp] theorem map_subtype {p : α → Prop} {l : Vector { x // p x } n}
    {f : { x // p x } → β} {g : α → β} (hf : ∀ x h, f ⟨x, h⟩ = g x) :
    l.map f = l.unattach.map g := by
  rcases l with ⟨l, rfl⟩
  simp [Array.map_subtype hf]

@[simp] theorem findSome?_subtype {p : α → Prop} {l : Array { x // p x }}
    {f : { x // p x } → Option β} {g : α → Option β} (hf : ∀ x h, f ⟨x, h⟩ = g x) :
    l.findSome? f = l.unattach.findSome? g := by
  rcases l with ⟨l, rfl⟩
  simp
  rw [Array.findSome?_subtype hf]

@[simp] theorem find?_subtype {p : α → Prop} {l : Array { x // p x }}
    {f : { x // p x } → Bool} {g : α → Bool} (hf : ∀ x h, f ⟨x, h⟩ = g x) :
    (l.find? f).map Subtype.val = l.unattach.find? g := by
  rcases l with ⟨l, rfl⟩
  simp
  rw [Array.find?_subtype hf]

/-! ### Simp lemmas pushing `unattach` inwards. -/

@[simp] theorem unattach_reverse {p : α → Prop} {l : Vector { x // p x } n} :
    l.reverse.unattach = l.unattach.reverse := by
  rcases l with ⟨l, rfl⟩
  simp [Array.unattach_reverse]


@[simp] theorem unattach_append {p : α → Prop} {l₁ l₂ : Vector { x // p x } n} :
    (l₁ ++ l₂).unattach = l₁.unattach ++ l₂.unattach := by
  rcases l₁
  rcases l₂
  simp

@[simp] theorem unattach_flatten {p : α → Prop} {l : Vector (Vector { x // p x } n) n} :
    l.flatten.unattach = (l.map unattach).flatten := by
  unfold unattach
  cases l using vector₂_induction
  simp only [flatten_mk, Array.map_map, Function.comp_apply, Array.map_subtype,
    Array.unattach_attach, Array.map_id_fun', id_eq, map_mk, Array.map_flatten, map_subtype,
    map_id_fun', unattach_mk, eq_mk]
  unfold Array.unattach
  rfl

@[simp] theorem unattach_mkVector {p : α → Prop} {n : Nat} {x : { x // p x }} :
    (mkVector n x).unattach = mkVector n x.1 := by
  simp [unattach]

end Vector

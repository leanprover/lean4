/-
Copyright (c) 2023 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
prelude
import Init.Data.List.Count
import Init.Data.Subtype

namespace List

/-- `O(n)`. Partial map. If `f : Π a, P a → β` is a partial function defined on
  `a : α` satisfying `P`, then `pmap f l h` is essentially the same as `map f l`
  but is defined only when all members of `l` satisfy `P`, using the proof
  to apply `f`. -/
@[simp] def pmap {P : α → Prop} (f : ∀ a, P a → β) : ∀ l : List α, (H : ∀ a ∈ l, P a) → List β
  | [], _ => []
  | a :: l, H => f a (forall_mem_cons.1 H).1 :: pmap f l (forall_mem_cons.1 H).2

/--
Unsafe implementation of `attachWith`, taking advantage of the fact that the representation of
`List {x // P x}` is the same as the input `List α`.
(Someday, the compiler might do this optimization automatically, but until then...)
-/
@[inline] private unsafe def attachWithImpl
    (l : List α) (P : α → Prop) (_ : ∀ x ∈ l, P x) : List {x // P x} := unsafeCast l

/-- `O(1)`. "Attach" a proof `P x` that holds for all the elements of `l` to produce a new list
  with the same elements but in the type `{x // P x}`. -/
@[implemented_by attachWithImpl] def attachWith
    (l : List α) (P : α → Prop) (H : ∀ x ∈ l, P x) : List {x // P x} := pmap Subtype.mk l H

/-- `O(1)`. "Attach" the proof that the elements of `l` are in `l` to produce a new list
  with the same elements but in the type `{x // x ∈ l}`. -/
@[inline] def attach (l : List α) : List {x // x ∈ l} := attachWith l _ fun _ => id

/-- Implementation of `pmap` using the zero-copy version of `attach`. -/
@[inline] private def pmapImpl {P : α → Prop} (f : ∀ a, P a → β) (l : List α) (H : ∀ a ∈ l, P a) :
    List β := (l.attachWith _ H).map fun ⟨x, h'⟩ => f x h'

@[csimp] private theorem pmap_eq_pmapImpl : @pmap = @pmapImpl := by
  funext α β p f L h'
  let rec go : ∀ L' (hL' : ∀ ⦃x⦄, x ∈ L' → p x),
      pmap f L' hL' = map (fun ⟨x, hx⟩ => f x hx) (pmap Subtype.mk L' hL')
  | nil, hL' => rfl
  | cons _ L', hL' => congrArg _ <| go L' fun _ hx => hL' (.tail _ hx)
  exact go L h'

@[simp] theorem attach_nil : ([] : List α).attach = [] := rfl

@[simp] theorem attachWith_nil : ([] : List α).attachWith P H = [] := rfl

@[simp]
theorem pmap_eq_map (p : α → Prop) (f : α → β) (l : List α) (H) :
    @pmap _ _ p (fun a _ => f a) l H = map f l := by
  induction l
  · rfl
  · simp only [*, pmap, map]

theorem pmap_congr_left {p q : α → Prop} {f : ∀ a, p a → β} {g : ∀ a, q a → β} (l : List α) {H₁ H₂}
    (h : ∀ a ∈ l, ∀ (h₁ h₂), f a h₁ = g a h₂) : pmap f l H₁ = pmap g l H₂ := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    rw [pmap, pmap, h _ (mem_cons_self _ _), ih fun a ha => h a (mem_cons_of_mem _ ha)]

@[deprecated pmap_congr_left (since := "2024-09-06")] abbrev pmap_congr := @pmap_congr_left

theorem map_pmap {p : α → Prop} (g : β → γ) (f : ∀ a, p a → β) (l H) :
    map g (pmap f l H) = pmap (fun a h => g (f a h)) l H := by
  induction l
  · rfl
  · simp only [*, pmap, map]

theorem pmap_map {p : β → Prop} (g : ∀ b, p b → γ) (f : α → β) (l H) :
    pmap g (map f l) H = pmap (fun a h => g (f a) h) l fun _ h => H _ (mem_map_of_mem _ h) := by
  induction l
  · rfl
  · simp only [*, pmap, map]

theorem attach_congr {l₁ l₂ : List α} (h : l₁ = l₂) :
    l₁.attach = l₂.attach.map (fun x => ⟨x.1, h ▸ x.2⟩) := by
  subst h
  simp

theorem attachWith_congr {l₁ l₂ : List α} (w : l₁ = l₂) {P : α → Prop} {H : ∀ x ∈ l₁, P x} :
    l₁.attachWith P H = l₂.attachWith P fun _ h => H _ (w ▸ h) := by
  subst w
  simp

@[simp] theorem attach_cons {x : α} {xs : List α} :
    (x :: xs).attach =
      ⟨x, mem_cons_self x xs⟩ :: xs.attach.map fun ⟨y, h⟩ => ⟨y, mem_cons_of_mem x h⟩ := by
  simp only [attach, attachWith, pmap, map_pmap, cons.injEq, true_and]
  apply pmap_congr_left
  intros a _ m' _
  rfl

@[simp]
theorem attachWith_cons {x : α} {xs : List α} {p : α → Prop} (h : ∀ a ∈ x :: xs, p a) :
    (x :: xs).attachWith p h = ⟨x, h x (mem_cons_self x xs)⟩ ::
      xs.attachWith p (fun a ha ↦ h a (mem_cons_of_mem x ha)) :=
  rfl

theorem pmap_eq_map_attach {p : α → Prop} (f : ∀ a, p a → β) (l H) :
    pmap f l H = l.attach.map fun x => f x.1 (H _ x.2) := by
  rw [attach, attachWith, map_pmap]; exact pmap_congr_left l fun _ _ _ _ => rfl

theorem attach_map_coe (l : List α) (f : α → β) :
    (l.attach.map fun (i : {i // i ∈ l}) => f i) = l.map f := by
  rw [attach, attachWith, map_pmap]; exact pmap_eq_map _ _ _ _

theorem attach_map_val (l : List α) (f : α → β) : (l.attach.map fun i => f i.val) = l.map f :=
  attach_map_coe _ _

@[simp]
theorem attach_map_subtype_val (l : List α) : l.attach.map Subtype.val = l :=
  (attach_map_coe _ _).trans (List.map_id _)

theorem attachWith_map_coe {p : α → Prop} (f : α → β) (l : List α) (H : ∀ a ∈ l, p a) :
    ((l.attachWith p H).map fun (i : { i // p i}) => f i) = l.map f := by
  rw [attachWith, map_pmap]; exact pmap_eq_map _ _ _ _

theorem attachWith_map_val {p : α → Prop} (f : α → β) (l : List α) (H : ∀ a ∈ l, p a) :
    ((l.attachWith p H).map fun i => f i.val) = l.map f :=
  attachWith_map_coe _ _ _

@[simp]
theorem attachWith_map_subtype_val {p : α → Prop} (l : List α) (H : ∀ a ∈ l, p a) :
    (l.attachWith p H).map Subtype.val = l :=
  (attachWith_map_coe _ _ _).trans (List.map_id _)

@[simp]
theorem mem_attach (l : List α) : ∀ x, x ∈ l.attach
  | ⟨a, h⟩ => by
    have := mem_map.1 (by rw [attach_map_subtype_val] <;> exact h)
    rcases this with ⟨⟨_, _⟩, m, rfl⟩
    exact m

@[simp]
theorem mem_pmap {p : α → Prop} {f : ∀ a, p a → β} {l H b} :
    b ∈ pmap f l H ↔ ∃ (a : _) (h : a ∈ l), f a (H a h) = b := by
  simp only [pmap_eq_map_attach, mem_map, mem_attach, true_and, Subtype.exists, eq_comm]

theorem mem_pmap_of_mem {p : α → Prop} {f : ∀ a, p a → β} {l H} {a} (h : a ∈ l) :
    f a (H a h) ∈ pmap f l H := by
  rw [mem_pmap]
  exact ⟨a, h, rfl⟩

@[simp]
theorem length_pmap {p : α → Prop} {f : ∀ a, p a → β} {l H} : length (pmap f l H) = length l := by
  induction l
  · rfl
  · simp only [*, pmap, length]

@[simp]
theorem length_attach {L : List α} : L.attach.length = L.length :=
  length_pmap

@[simp]
theorem length_attachWith {p : α → Prop} {l H} : length (l.attachWith p H) = length l :=
  length_pmap

@[simp]
theorem pmap_eq_nil_iff {p : α → Prop} {f : ∀ a, p a → β} {l H} : pmap f l H = [] ↔ l = [] := by
  rw [← length_eq_zero, length_pmap, length_eq_zero]

theorem pmap_ne_nil_iff {P : α → Prop} (f : (a : α) → P a → β) {xs : List α}
    (H : ∀ (a : α), a ∈ xs → P a) : xs.pmap f H ≠ [] ↔ xs ≠ [] := by
  simp

theorem pmap_eq_self {l : List α} {p : α → Prop} (hp : ∀ (a : α), a ∈ l → p a)
    (f : (a : α) → p a → α) : l.pmap f hp = l ↔ ∀ a (h : a ∈ l), f a (hp a h) = a := by
  rw [pmap_eq_map_attach]
  conv => lhs; rhs; rw [← attach_map_subtype_val l]
  rw [map_inj_left]
  simp

@[simp]
theorem attach_eq_nil_iff {l : List α} : l.attach = [] ↔ l = [] :=
  pmap_eq_nil_iff

theorem attach_ne_nil_iff {l : List α} : l.attach ≠ [] ↔ l ≠ [] :=
  pmap_ne_nil_iff _ _

@[simp]
theorem attachWith_eq_nil_iff {l : List α} {P : α → Prop} {H : ∀ a ∈ l, P a} :
    l.attachWith P H = [] ↔ l = [] :=
  pmap_eq_nil_iff

theorem attachWith_ne_nil_iff {l : List α} {P : α → Prop} {H : ∀ a ∈ l, P a} :
    l.attachWith P H ≠ [] ↔ l ≠ [] :=
  pmap_ne_nil_iff _ _

@[deprecated pmap_eq_nil_iff (since := "2024-09-06")] abbrev pmap_eq_nil := @pmap_eq_nil_iff
@[deprecated pmap_ne_nil_iff (since := "2024-09-06")] abbrev pmap_ne_nil := @pmap_ne_nil_iff
@[deprecated attach_eq_nil_iff (since := "2024-09-06")] abbrev attach_eq_nil := @attach_eq_nil_iff
@[deprecated attach_ne_nil_iff (since := "2024-09-06")] abbrev attach_ne_nil := @attach_ne_nil_iff

@[simp]
theorem getElem?_pmap {p : α → Prop} (f : ∀ a, p a → β) {l : List α} (h : ∀ a ∈ l, p a) (n : Nat) :
    (pmap f l h)[n]? = Option.pmap f l[n]? fun x H => h x (getElem?_mem H) := by
  induction l generalizing n with
  | nil => simp
  | cons hd tl hl =>
    rcases n with ⟨n⟩
    · simp only [Option.pmap]
      split <;> simp_all
    · simp only [hl, pmap, Option.pmap, getElem?_cons_succ]
      split <;> rename_i h₁ _ <;> split <;> rename_i h₂ _
      · simp_all
      · simp at h₂
        simp_all
      · simp_all
      · simp_all

theorem get?_pmap {p : α → Prop} (f : ∀ a, p a → β) {l : List α} (h : ∀ a ∈ l, p a) (n : Nat) :
    get? (pmap f l h) n = Option.pmap f (get? l n) fun x H => h x (get?_mem H) := by
  simp only [get?_eq_getElem?]
  simp [getElem?_pmap, h]

@[simp]
theorem getElem_pmap {p : α → Prop} (f : ∀ a, p a → β) {l : List α} (h : ∀ a ∈ l, p a) {n : Nat}
    (hn : n < (pmap f l h).length) :
    (pmap f l h)[n] =
      f (l[n]'(@length_pmap _ _ p f l h ▸ hn))
        (h _ (getElem_mem (@length_pmap _ _ p f l h ▸ hn))) := by
  induction l generalizing n with
  | nil =>
    simp only [length, pmap] at hn
    exact absurd hn (Nat.not_lt_of_le n.zero_le)
  | cons hd tl hl =>
    cases n
    · simp
    · simp [hl]

theorem get_pmap {p : α → Prop} (f : ∀ a, p a → β) {l : List α} (h : ∀ a ∈ l, p a) {n : Nat}
    (hn : n < (pmap f l h).length) :
    get (pmap f l h) ⟨n, hn⟩ =
      f (get l ⟨n, @length_pmap _ _ p f l h ▸ hn⟩)
        (h _ (get_mem l n (@length_pmap _ _ p f l h ▸ hn))) := by
  simp only [get_eq_getElem]
  simp [getElem_pmap]

@[simp]
theorem getElem?_attachWith {xs : List α} {i : Nat} {P : α → Prop} {H : ∀ a ∈ xs, P a} :
    (xs.attachWith P H)[i]? = xs[i]?.pmap Subtype.mk (fun _ a => H _ (getElem?_mem a)) :=
  getElem?_pmap ..

@[simp]
theorem getElem?_attach {xs : List α} {i : Nat} :
    xs.attach[i]? = xs[i]?.pmap Subtype.mk (fun _ a => getElem?_mem a) :=
  getElem?_attachWith

@[simp]
theorem getElem_attachWith {xs : List α} {P : α → Prop} {H : ∀ a ∈ xs, P a}
    {i : Nat} (h : i < (xs.attachWith P H).length) :
    (xs.attachWith P H)[i] = ⟨xs[i]'(by simpa using h), H _ (getElem_mem (by simpa using h))⟩ :=
  getElem_pmap ..

@[simp]
theorem getElem_attach {xs : List α} {i : Nat} (h : i < xs.attach.length) :
    xs.attach[i] = ⟨xs[i]'(by simpa using h), getElem_mem (by simpa using h)⟩ :=
  getElem_attachWith h

@[simp] theorem head?_pmap {P : α → Prop} (f : (a : α) → P a → β) (xs : List α)
    (H : ∀ (a : α), a ∈ xs → P a) :
    (xs.pmap f H).head? = xs.attach.head?.map fun ⟨a, m⟩ => f a (H a m) := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp at ih
    simp [head?_pmap, ih]

@[simp] theorem head_pmap {P : α → Prop} (f : (a : α) → P a → β) (xs : List α)
    (H : ∀ (a : α), a ∈ xs → P a) (h : xs.pmap f H ≠ []) :
    (xs.pmap f H).head h = f (xs.head (by simpa using h)) (H _ (head_mem _)) := by
  induction xs with
  | nil => simp at h
  | cons x xs ih => simp [head_pmap, ih]

@[simp] theorem head?_attachWith {P : α → Prop} {xs : List α}
    (H : ∀ (a : α), a ∈ xs → P a) :
    (xs.attachWith P H).head? = xs.head?.pbind (fun a h => some ⟨a, H _ (mem_of_mem_head? h)⟩) := by
  cases xs <;> simp_all

@[simp] theorem head_attachWith {P : α → Prop} {xs : List α}
    {H : ∀ (a : α), a ∈ xs → P a} (h : xs.attachWith P H ≠ []) :
    (xs.attachWith P H).head h = ⟨xs.head (by simpa using h), H _ (head_mem _)⟩ := by
  cases xs with
  | nil => simp at h
  | cons x xs => simp [head_attachWith, h]

@[simp] theorem head?_attach (xs : List α) :
    xs.attach.head? = xs.head?.pbind (fun a h => some ⟨a, mem_of_mem_head? h⟩) := by
  cases xs <;> simp_all

@[simp] theorem head_attach {xs : List α} (h) :
    xs.attach.head h = ⟨xs.head (by simpa using h), head_mem (by simpa using h)⟩ := by
  cases xs with
  | nil => simp at h
  | cons x xs => simp [head_attach, h]

@[simp] theorem tail_pmap {P : α → Prop} (f : (a : α) → P a → β) (xs : List α)
    (H : ∀ (a : α), a ∈ xs → P a) :
    (xs.pmap f H).tail = xs.tail.pmap f (fun a h => H a (mem_of_mem_tail h)) := by
  cases xs <;> simp

@[simp] theorem tail_attachWith {P : α → Prop} {xs : List α}
    {H : ∀ (a : α), a ∈ xs → P a} :
    (xs.attachWith P H).tail = xs.tail.attachWith P (fun a h => H a (mem_of_mem_tail h)) := by
  cases xs <;> simp

@[simp] theorem tail_attach (xs : List α) :
    xs.attach.tail = xs.tail.attach.map (fun ⟨x, h⟩ => ⟨x, mem_of_mem_tail h⟩) := by
  cases xs <;> simp

theorem foldl_pmap (l : List α) {P : α → Prop} (f : (a : α) → P a → β)
  (H : ∀ (a : α), a ∈ l → P a) (g : γ → β → γ) (x : γ) :
    (l.pmap f H).foldl g x = l.attach.foldl (fun acc a => g acc (f a.1 (H _ a.2))) x := by
  rw [pmap_eq_map_attach, foldl_map]

theorem foldr_pmap (l : List α) {P : α → Prop} (f : (a : α) → P a → β)
  (H : ∀ (a : α), a ∈ l → P a) (g : β → γ → γ) (x : γ) :
    (l.pmap f H).foldr g x = l.attach.foldr (fun a acc => g (f a.1 (H _ a.2)) acc) x := by
  rw [pmap_eq_map_attach, foldr_map]

/--
If we fold over `l.attach` with a function that ignores the membership predicate,
we get the same results as folding over `l` directly.

This is useful when we need to use `attach` to show termination.

Unfortunately this can't be applied by `simp` because of the higher order unification problem,
and even when rewriting we need to specify the function explicitly.
-/
theorem foldl_attach (l : List α) (f : β → α → β) (b : β) :
    l.attach.foldl (fun acc t => f acc t.1) b = l.foldl f b := by
  induction l generalizing b with
  | nil => simp
  | cons a l ih => rw [foldl_cons, attach_cons, foldl_cons, foldl_map, ih]

/--
If we fold over `l.attach` with a function that ignores the membership predicate,
we get the same results as folding over `l` directly.

This is useful when we need to use `attach` to show termination.

Unfortunately this can't be applied by `simp` because of the higher order unification problem,
and even when rewriting we need to specify the function explicitly.
-/
theorem foldr_attach (l : List α) (f : α → β → β) (b : β) :
    l.attach.foldr (fun t acc => f t.1 acc) b = l.foldr f b := by
  induction l generalizing b with
  | nil => simp
  | cons a l ih => rw [foldr_cons, attach_cons, foldr_cons, foldr_map, ih]

theorem attach_map {l : List α} (f : α → β) :
    (l.map f).attach = l.attach.map (fun ⟨x, h⟩ => ⟨f x, mem_map_of_mem f h⟩) := by
  induction l <;> simp [*]

theorem attachWith_map {l : List α} (f : α → β) {P : β → Prop} {H : ∀ (b : β), b ∈ l.map f → P b} :
    (l.map f).attachWith P H = (l.attachWith (P ∘ f) (fun _ h => H _ (mem_map_of_mem f h))).map
      fun ⟨x, h⟩ => ⟨f x, h⟩ := by
  induction l <;> simp [*]

theorem map_attachWith {l : List α} {P : α → Prop} {H : ∀ (a : α), a ∈ l → P a}
    (f : { x // P x } → β) :
    (l.attachWith P H).map f =
      l.pmap (fun a (h : a ∈ l ∧ P a) => f ⟨a, H _ h.1⟩) (fun a h => ⟨h, H a h⟩) := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [attachWith_cons, map_cons, ih, pmap, cons.injEq, true_and]
    apply pmap_congr_left
    simp

/-- See also `pmap_eq_map_attach` for writing `pmap` in terms of `map` and `attach`. -/
theorem map_attach {l : List α} (f : { x // x ∈ l } → β) :
    l.attach.map f = l.pmap (fun a h => f ⟨a, h⟩) (fun _ => id) := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [attach_cons, map_cons, map_map, Function.comp_apply, pmap, cons.injEq, true_and, ih]
    apply pmap_congr_left
    simp

theorem attach_filterMap {l : List α} {f : α → Option β} :
    (l.filterMap f).attach = l.attach.filterMap
      fun ⟨x, h⟩ => (f x).pbind (fun b m => some ⟨b, mem_filterMap.mpr ⟨x, h, m⟩⟩) := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [filterMap_cons, attach_cons, ih, filterMap_map]
    split <;> rename_i h
    · simp only [Option.pbind_eq_none_iff, reduceCtorEq, Option.mem_def, exists_false,
        or_false] at h
      rw [attach_congr]
      rotate_left
      · simp only [h]
        rfl
      rw [ih]
      simp only [map_filterMap, Option.map_pbind, Option.map_some']
      rfl
    · simp only [Option.pbind_eq_some_iff] at h
      obtain ⟨a, h, w⟩ := h
      simp only [Option.some.injEq] at w
      subst w
      simp only [Option.mem_def] at h
      rw [attach_congr]
      rotate_left
      · simp only [h]
        rfl
      rw [attach_cons, map_cons, map_map, ih, map_filterMap]
      congr
      ext
      simp

theorem attach_filter {l : List α} (p : α → Bool) :
    (l.filter p).attach = l.attach.filterMap
      fun x => if w : p x.1 then some ⟨x.1, mem_filter.mpr ⟨x.2, w⟩⟩ else none := by
  rw [attach_congr (congrFun (filterMap_eq_filter _).symm _), attach_filterMap, map_filterMap]
  simp only [Option.guard]
  congr
  ext1
  split <;> simp

-- We are still missing here `attachWith_filterMap` and `attachWith_filter`.
-- Also missing are `filterMap_attach`, `filter_attach`, `filterMap_attachWith` and `filter_attachWith`.

theorem pmap_pmap {p : α → Prop} {q : β → Prop} (g : ∀ a, p a → β) (f : ∀ b, q b → γ) (l H₁ H₂) :
    pmap f (pmap g l H₁) H₂ =
      pmap (α := { x // x ∈ l }) (fun a h => f (g a h) (H₂ (g a h) (mem_pmap_of_mem a.2))) l.attach
        (fun a _ => H₁ a a.2) := by
  simp [pmap_eq_map_attach, attach_map]

@[simp] theorem pmap_append {p : ι → Prop} (f : ∀ a : ι, p a → α) (l₁ l₂ : List ι)
    (h : ∀ a ∈ l₁ ++ l₂, p a) :
    (l₁ ++ l₂).pmap f h =
      (l₁.pmap f fun a ha => h a (mem_append_left l₂ ha)) ++
        l₂.pmap f fun a ha => h a (mem_append_right l₁ ha) := by
  induction l₁ with
  | nil => rfl
  | cons _ _ ih =>
    dsimp only [pmap, cons_append]
    rw [ih]

theorem pmap_append' {p : α → Prop} (f : ∀ a : α, p a → β) (l₁ l₂ : List α)
    (h₁ : ∀ a ∈ l₁, p a) (h₂ : ∀ a ∈ l₂, p a) :
    ((l₁ ++ l₂).pmap f fun a ha => (List.mem_append.1 ha).elim (h₁ a) (h₂ a)) =
      l₁.pmap f h₁ ++ l₂.pmap f h₂ :=
  pmap_append f l₁ l₂ _

@[simp] theorem attach_append (xs ys : List α) :
    (xs ++ ys).attach = xs.attach.map (fun ⟨x, h⟩ => ⟨x, mem_append_of_mem_left ys h⟩) ++
      ys.attach.map fun ⟨x, h⟩ => ⟨x, mem_append_of_mem_right xs h⟩ := by
  simp only [attach, attachWith, pmap, map_pmap, pmap_append]
  congr 1 <;>
  exact pmap_congr_left _ fun _ _ _ _ => rfl

@[simp] theorem attachWith_append {P : α → Prop} {xs ys : List α}
    {H : ∀ (a : α), a ∈ xs ++ ys → P a} :
    (xs ++ ys).attachWith P H = xs.attachWith P (fun a h => H a (mem_append_of_mem_left ys h)) ++
      ys.attachWith P (fun a h => H a (mem_append_of_mem_right xs h)) := by
  simp only [attachWith, attach_append, map_pmap, pmap_append]

@[simp] theorem pmap_reverse {P : α → Prop} (f : (a : α) → P a → β) (xs : List α)
    (H : ∀ (a : α), a ∈ xs.reverse → P a) :
    xs.reverse.pmap f H = (xs.pmap f (fun a h => H a (by simpa using h))).reverse := by
  induction xs <;> simp_all

theorem reverse_pmap {P : α → Prop} (f : (a : α) → P a → β) (xs : List α)
    (H : ∀ (a : α), a ∈ xs → P a) :
    (xs.pmap f H).reverse = xs.reverse.pmap f (fun a h => H a (by simpa using h)) := by
  rw [pmap_reverse]

@[simp] theorem attachWith_reverse {P : α → Prop} {xs : List α}
    {H : ∀ (a : α), a ∈ xs.reverse → P a} :
    xs.reverse.attachWith P H =
      (xs.attachWith P (fun a h => H a (by simpa using h))).reverse :=
  pmap_reverse ..

theorem reverse_attachWith {P : α → Prop} {xs : List α}
    {H : ∀ (a : α), a ∈ xs → P a} :
    (xs.attachWith P H).reverse = (xs.reverse.attachWith P (fun a h => H a (by simpa using h))) :=
  reverse_pmap ..

@[simp] theorem attach_reverse (xs : List α) :
    xs.reverse.attach = xs.attach.reverse.map fun ⟨x, h⟩ => ⟨x, by simpa using h⟩ := by
  simp only [attach, attachWith, reverse_pmap, map_pmap]
  apply pmap_congr_left
  intros
  rfl

theorem reverse_attach (xs : List α) :
    xs.attach.reverse = xs.reverse.attach.map fun ⟨x, h⟩ => ⟨x, by simpa using h⟩ := by
  simp only [attach, attachWith, reverse_pmap, map_pmap]
  apply pmap_congr_left
  intros
  rfl

@[simp] theorem getLast?_pmap {P : α → Prop} (f : (a : α) → P a → β) (xs : List α)
    (H : ∀ (a : α), a ∈ xs → P a) :
    (xs.pmap f H).getLast? = xs.attach.getLast?.map fun ⟨a, m⟩ => f a (H a m) := by
  simp only [getLast?_eq_head?_reverse]
  rw [reverse_pmap, reverse_attach, head?_map, pmap_eq_map_attach, head?_map]
  simp only [Option.map_map]
  congr

@[simp] theorem getLast_pmap {P : α → Prop} (f : (a : α) → P a → β) (xs : List α)
    (H : ∀ (a : α), a ∈ xs → P a) (h : xs.pmap f H ≠ []) :
    (xs.pmap f H).getLast h = f (xs.getLast (by simpa using h)) (H _ (getLast_mem _)) := by
  simp only [getLast_eq_head_reverse]
  simp only [reverse_pmap, head_pmap, head_reverse]

@[simp] theorem getLast?_attachWith {P : α → Prop} {xs : List α}
    {H : ∀ (a : α), a ∈ xs → P a} :
    (xs.attachWith P H).getLast? = xs.getLast?.pbind (fun a h => some ⟨a, H _ (mem_of_getLast?_eq_some h)⟩) := by
  rw [getLast?_eq_head?_reverse, reverse_attachWith, head?_attachWith]
  simp

@[simp] theorem getLast_attachWith {P : α → Prop} {xs : List α}
    {H : ∀ (a : α), a ∈ xs → P a} (h : xs.attachWith P H ≠ []) :
    (xs.attachWith P H).getLast h = ⟨xs.getLast (by simpa using h), H _ (getLast_mem _)⟩ := by
  simp only [getLast_eq_head_reverse, reverse_attachWith, head_attachWith, head_map]

@[simp]
theorem getLast?_attach {xs : List α} :
    xs.attach.getLast? = xs.getLast?.pbind fun a h => some ⟨a, mem_of_getLast?_eq_some h⟩ := by
  rw [getLast?_eq_head?_reverse, reverse_attach, head?_map, head?_attach]
  simp

@[simp]
theorem getLast_attach {xs : List α} (h : xs.attach ≠ []) :
    xs.attach.getLast h = ⟨xs.getLast (by simpa using h), getLast_mem (by simpa using h)⟩ := by
  simp only [getLast_eq_head_reverse, reverse_attach, head_map, head_attach]

@[simp]
theorem countP_attach (l : List α) (p : α → Bool) :
    l.attach.countP (fun a : {x // x ∈ l} => p a) = l.countP p := by
  simp only [← Function.comp_apply (g := Subtype.val), ← countP_map, attach_map_subtype_val]

@[simp]
theorem countP_attachWith {p : α → Prop} (l : List α) (H : ∀ a ∈ l, p a) (q : α → Bool) :
    (l.attachWith p H).countP (fun a : {x // p x} => q a) = l.countP q := by
  simp only [← Function.comp_apply (g := Subtype.val), ← countP_map, attachWith_map_subtype_val]

@[simp]
theorem count_attach [DecidableEq α] (l : List α) (a : {x // x ∈ l}) :
    l.attach.count a = l.count ↑a :=
  Eq.trans (countP_congr fun _ _ => by simp [Subtype.ext_iff]) <| countP_attach _ _

@[simp]
theorem count_attachWith [DecidableEq α] {p : α → Prop} (l : List α) (H : ∀ a ∈ l, p a) (a : {x // p x}) :
    (l.attachWith p H).count a = l.count ↑a :=
  Eq.trans (countP_congr fun _ _ => by simp [Subtype.ext_iff]) <| countP_attachWith _ _ _

/-! ## unattach

`List.unattach` is the (one-sided) inverse of `List.attach`. It is a synonym for `List.map Subtype.val`.

We use it by providing a simp lemma `l.attach.unattach = l`, and simp lemmas which recognize higher order
functions applied to `l : List { x // p x }` which only depend on the value, not the predicate, and rewrite these
in terms of a simpler function applied to `l.unattach`.

Further, we provide simp lemmas that push `unattach` inwards.
-/

/--
A synonym for `l.map (·.val)`. Mostly this should not be needed by users.
It is introduced as an intermediate step by lemmas such as `map_subtype`,
and is ideally subsequently simplified away by `unattach_attach`.

If not, usually the right approach is `simp [List.unattach, -List.map_subtype]` to unfold.
-/
def unattach {α : Type _} {p : α → Prop} (l : List { x // p x }) := l.map (·.val)

@[simp] theorem unattach_nil {p : α → Prop} : ([] : List { x // p x }).unattach = [] := rfl
@[simp] theorem unattach_cons {p : α → Prop} {a : { x // p x }} {l : List { x // p x }} :
  (a :: l).unattach = a.val :: l.unattach := rfl

@[simp] theorem length_unattach {p : α → Prop} {l : List { x // p x }} :
    l.unattach.length = l.length := by
  unfold unattach
  simp

@[simp] theorem unattach_attach {l : List α} : l.attach.unattach = l := by
  unfold unattach
  induction l with
  | nil => simp
  | cons a l ih => simp [ih, Function.comp_def]

@[simp] theorem unattach_attachWith {p : α → Prop} {l : List α}
    {H : ∀ a ∈ l, p a} :
    (l.attachWith p H).unattach = l := by
  unfold unattach
  induction l with
  | nil => simp
  | cons a l ih => simp [ih, Function.comp_def]

/-! ### Recognizing higher order functions on subtypes using a function that only depends on the value. -/

/--
This lemma identifies folds over lists of subtypes, where the function only depends on the value, not the proposition,
and simplifies these to the function directly taking the value.
-/
@[simp] theorem foldl_subtype {p : α → Prop} {l : List { x // p x }}
    {f : β → { x // p x } → β} {g : β → α → β} {x : β}
    {hf : ∀ b x h, f b ⟨x, h⟩ = g b x} :
    l.foldl f x = l.unattach.foldl g x := by
  unfold unattach
  induction l generalizing x with
  | nil => simp
  | cons a l ih => simp [ih, hf]

/--
This lemma identifies folds over lists of subtypes, where the function only depends on the value, not the proposition,
and simplifies these to the function directly taking the value.
-/
@[simp] theorem foldr_subtype {p : α → Prop} {l : List { x // p x }}
    {f : { x // p x } → β → β} {g : α → β → β} {x : β}
    {hf : ∀ x h b, f ⟨x, h⟩ b = g x b} :
    l.foldr f x = l.unattach.foldr g x := by
  unfold unattach
  induction l generalizing x with
  | nil => simp
  | cons a l ih => simp [ih, hf]

/--
This lemma identifies maps over lists of subtypes, where the function only depends on the value, not the proposition,
and simplifies these to the function directly taking the value.
-/
@[simp] theorem map_subtype {p : α → Prop} {l : List { x // p x }}
    {f : { x // p x } → β} {g : α → β} {hf : ∀ x h, f ⟨x, h⟩ = g x} :
    l.map f = l.unattach.map g := by
  unfold unattach
  induction l with
  | nil => simp
  | cons a l ih => simp [ih, hf]

@[simp] theorem filterMap_subtype {p : α → Prop} {l : List { x // p x }}
    {f : { x // p x } → Option β} {g : α → Option β} {hf : ∀ x h, f ⟨x, h⟩ = g x} :
    l.filterMap f = l.unattach.filterMap g := by
  unfold unattach
  induction l with
  | nil => simp
  | cons a l ih => simp [ih, hf, filterMap_cons]

@[simp] theorem flatMap_subtype {p : α → Prop} {l : List { x // p x }}
    {f : { x // p x } → List β} {g : α → List β} {hf : ∀ x h, f ⟨x, h⟩ = g x} :
    (l.flatMap f) = l.unattach.flatMap g := by
  unfold unattach
  induction l with
  | nil => simp
  | cons a l ih => simp [ih, hf]

@[deprecated flatMap_subtype (since := "2024-10-16")] abbrev bind_subtype := @flatMap_subtype

@[simp] theorem unattach_filter {p : α → Prop} {l : List { x // p x }}
    {f : { x // p x } → Bool} {g : α → Bool} {hf : ∀ x h, f ⟨x, h⟩ = g x} :
    (l.filter f).unattach = l.unattach.filter g := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [filter_cons, hf, unattach_cons]
    split <;> simp [ih]

/-! ### Simp lemmas pushing `unattach` inwards. -/

@[simp] theorem unattach_reverse {p : α → Prop} {l : List { x // p x }} :
    l.reverse.unattach = l.unattach.reverse := by
  simp [unattach, -map_subtype]

@[simp] theorem unattach_append {p : α → Prop} {l₁ l₂ : List { x // p x }} :
    (l₁ ++ l₂).unattach = l₁.unattach ++ l₂.unattach := by
  simp [unattach, -map_subtype]

@[simp] theorem unattach_flatten {p : α → Prop} {l : List (List { x // p x })} :
    l.flatten.unattach = (l.map unattach).flatten := by
  unfold unattach
  induction l <;> simp_all

@[deprecated unattach_flatten (since := "2024-10-14")] abbrev unattach_join := @unattach_flatten

@[simp] theorem unattach_replicate {p : α → Prop} {n : Nat} {x : { x // p x }} :
    (List.replicate n x).unattach = List.replicate n x.1 := by
  simp [unattach, -map_subtype]

end List

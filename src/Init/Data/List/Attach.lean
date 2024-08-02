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

@[simp]
theorem pmap_eq_map (p : α → Prop) (f : α → β) (l : List α) (H) :
    @pmap _ _ p (fun a _ => f a) l H = map f l := by
  induction l
  · rfl
  · simp only [*, pmap, map]

theorem pmap_congr {p q : α → Prop} {f : ∀ a, p a → β} {g : ∀ a, q a → β} (l : List α) {H₁ H₂}
    (h : ∀ a ∈ l, ∀ (h₁ h₂), f a h₁ = g a h₂) : pmap f l H₁ = pmap g l H₂ := by
  induction l with
  | nil => rfl
  | cons x l ih => rw [pmap, pmap, h _ (mem_cons_self _ _), ih fun a ha => h a (mem_cons_of_mem _ ha)]

theorem map_pmap {p : α → Prop} (g : β → γ) (f : ∀ a, p a → β) (l H) :
    map g (pmap f l H) = pmap (fun a h => g (f a h)) l H := by
  induction l
  · rfl
  · simp only [*, pmap, map]

theorem pmap_map {p : β → Prop} (g : ∀ b, p b → γ) (f : α → β) (l H) :
    pmap g (map f l) H = pmap (fun a h => g (f a) h) l fun a h => H _ (mem_map_of_mem _ h) := by
  induction l
  · rfl
  · simp only [*, pmap, map]

theorem pmap_eq_map_attach {p : α → Prop} (f : ∀ a, p a → β) (l H) :
    pmap f l H = l.attach.map fun x => f x.1 (H _ x.2) := by
  rw [attach, attachWith, map_pmap]; exact pmap_congr l fun _ _ _ _ => rfl

theorem attach_map_coe (l : List α) (f : α → β) :
    (l.attach.map fun (i : {i // i ∈ l}) => f i) = l.map f := by
  rw [attach, attachWith, map_pmap]; exact pmap_eq_map _ _ _ _

theorem attach_map_val (l : List α) (f : α → β) : (l.attach.map fun i => f i.val) = l.map f :=
  attach_map_coe _ _

@[simp]
theorem attach_map_subtype_val (l : List α) : l.attach.map Subtype.val = l :=
  (attach_map_coe _ _).trans l.map_id

theorem countP_attach (l : List α) (p : α → Bool) : l.attach.countP (fun a : {x // x ∈ l} => p a) = l.countP p := by
  simp only [← Function.comp_apply (g := Subtype.val), ← countP_map, attach_map_subtype_val]

@[simp]
theorem count_attach [DecidableEq α] (l : List α) (a : {x // x ∈ l}) : l.attach.count a = l.count ↑a :=
  Eq.trans (countP_congr fun _ _ => by simp [Subtype.ext_iff]) <| countP_attach _ _

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

@[simp]
theorem length_pmap {p : α → Prop} {f : ∀ a, p a → β} {l H} : length (pmap f l H) = length l := by
  induction l
  · rfl
  · simp only [*, pmap, length]

@[simp]
theorem length_attach (L : List α) : L.attach.length = L.length :=
  length_pmap

@[simp]
theorem pmap_eq_nil {p : α → Prop} {f : ∀ a, p a → β} {l H} : pmap f l H = [] ↔ l = [] := by
  rw [← length_eq_zero, length_pmap, length_eq_zero]

@[simp]
theorem attach_eq_nil (l : List α) : l.attach = [] ↔ l = [] :=
  pmap_eq_nil

theorem getLast_pmap (p : α → Prop) (f : ∀ a, p a → β) (l : List α)
    (hl₁ : ∀ a ∈ l, p a) (hl₂ : l ≠ []) :
    (l.pmap f hl₁).getLast (mt List.pmap_eq_nil.1 hl₂) =
      f (l.getLast hl₂) (hl₁ _ (List.getLast_mem hl₂)) := by
  induction l with
  | nil => apply (hl₂ rfl).elim
  | cons l_hd l_tl l_ih =>
    by_cases hl_tl : l_tl = []
    · simp [hl_tl]
    · simp only [pmap]
      rw [getLast_cons, l_ih _ hl_tl]
      simp only [getLast_cons hl_tl]

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

theorem getElem_pmap {p : α → Prop} (f : ∀ a, p a → β) {l : List α} (h : ∀ a ∈ l, p a) {n : Nat}
    (hn : n < (pmap f l h).length) :
    (pmap f l h)[n] =
      f (l[n]'(@length_pmap _ _ p f l h ▸ hn))
        (h _ (getElem_mem l n (@length_pmap _ _ p f l h ▸ hn))) := by
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

theorem pmap_append {p : ι → Prop} (f : ∀ a : ι, p a → α) (l₁ l₂ : List ι)
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

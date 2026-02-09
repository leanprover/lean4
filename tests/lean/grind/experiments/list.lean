/-!
This file consists of everything from `Init.Data.List.Lemmas` that `grind` doesn't deal with effortlessly,
sometimes with incomplete efforts to `grindify` the proofs.

It may still be a good source of ideas for `grind` attributes, or `grind` bugs!
But it's also fine to just delete it at some point.
-/

-- Rejected `grind` attributes:
-- attribute [grind] List.getElem?_eq_getElem -- This is way too slow, it adds about 30% time to this file.
-- attribute [grind] List.not_mem_nil -- unnecessary
-- attribute [grind →] List.length_eq_of_beq -- very bad!
-- attribute [grind] List.getLastD_concat
-- attribute [grind] List.head?_eq_getElem?
-- attribute [grind] LawfulMonad.bind_assoc -- time out?
-- attribute [grind] List.getLast?_flatten
-- attribute [grind] List.getElem?_eq_getElem -- too slow

namespace List'

open List Nat

/-! ## Preliminaries -/

/-! ### length -/


-- theorem exists_mem_of_length_pos : ∀ {l : List α}, 0 < length l → ∃ a, a ∈ l := by grind

-- theorem length_pos_iff_exists_mem {l : List α} : 0 < length l ↔ ∃ a, a ∈ l := by grind

-- theorem exists_mem_of_length_eq_add_one :
--     ∀ {l : List α}, l.length = n + 1 → ∃ a, a ∈ l := by grind

-- theorem exists_cons_of_length_pos : ∀ {l : List α}, 0 < l.length → ∃ h t, l = h :: t := by grind

-- theorem length_pos_iff_exists_cons :
--     ∀ {l : List α}, 0 < l.length ↔ ∃ h t, l = h :: t := by grind

-- theorem exists_cons_of_length_eq_add_one :
--     ∀ {l : List α}, l.length = n + 1 → ∃ h t, l = h :: t := by grind

-- theorem length_eq_one_iff {l : List α} : length l = 1 ↔ ∃ a, l = [a] := by grind

/-! ### cons -/

-- theorem cons_ne_self (a : α) (l : List α) : a :: l ≠ l := by grind

-- theorem ne_cons_self {a : α} {l : List α} : l ≠ a :: l := by grind

-- theorem exists_cons_of_ne_nil : ∀ {l : List α}, l ≠ [] → ∃ b l', l = b :: l' := by grind

-- theorem ne_nil_iff_exists_cons {l : List α} : l ≠ [] ↔ ∃ b l', l = b :: l' := by grind

-- theorem concat_ne_nil (a : α) (l : List α) : l ++ [a] ≠ [] := by grind

/-! ## L[i] and L[i]? -/

/-! ### getElem? and getElem -/

@[ext] theorem ext_getElem? {l₁ l₂ : List α} (h : ∀ i : Nat, l₁[i]? = l₂[i]?) : l₁ = l₂ :=
  match l₁, l₂, h with
  | [], [], _ => by grind
  | _ :: _, [], h => by simpa using h 0
  | [], _ :: _, h => by simpa using h 0
  | a :: l₁, a' :: l₂, h => by
    have h0 : some a = some a' := by simpa using h 0
    injection h0 with aa
    simp only [aa, ext_getElem? fun n => by simpa using h (n+1)]

/-! ### mem -/

theorem getElem_of_mem : ∀ {a} {l : List α}, a ∈ l → ∃ (i : Nat) (h : i < l.length), l[i]'h = a
  | _, _ :: _, .head .. => ⟨0, by grind⟩
  | _, _ :: _, .tail _ m => let ⟨i, h, e⟩ := getElem_of_mem m; ⟨i+1, by grind, by grind⟩

theorem mem_iff_getElem {a} {l : List α} : a ∈ l ↔ ∃ (i : Nat) (h : i < l.length), l[i]'h = a :=
  ⟨getElem_of_mem, by grind⟩

theorem mem_iff_getElem? {a} {l : List α} : a ∈ l ↔ ∃ i : Nat, l[i]? = some a := by
  simp [getElem?_eq_some_iff, mem_iff_getElem]

theorem forall_getElem {l : List α} {p : α → Prop} :
    (∀ (i : Nat) h, p (l[i]'h)) ↔ ∀ a, a ∈ l → p a := by
  induction l with
  | nil => grind
  | cons a l ih =>
    simp only [length_cons, mem_cons, forall_eq_or_imp]
    constructor
    · intro w
      constructor
      · exact w 0 (by grind)
      · grind
    · rintro ⟨h, w⟩ (_ | n) <;> grind

/-! ### `isEmpty` -/

theorem isEmpty_eq_false_iff_exists_mem {xs : List α} :
    xs.isEmpty = false ↔ ∃ x, x ∈ xs := by
  cases xs <;> simp

/-! ### any / all -/

-- Consider `attribute [grind PartialEquivBEq.symm]`?
theorem any_beq' [BEq α] [PartialEquivBEq α] {l : List α} :
    (l.any fun x => x == a) = l.contains a := by
  induction l with grind [PartialEquivBEq.symm]

/-- Variant of `all_bne` with `!=` reversed. -/
theorem all_bne' [BEq α] [PartialEquivBEq α] {l : List α} :
    (l.all fun x => x != a) = !l.contains a := by
  simp only [bne_comm, all_bne]

/-! ### set -/

theorem set_getElem_self {as : List α} {i : Nat} (h : i < as.length) :
    as.set i as[i] = as := by
  -- `grind` fails, `grind +extAll` loops forever
  apply ext_getElem <;> grind

theorem mem_set {l : List α} {i : Nat} (h : i < l.length) (a : α) :
    a ∈ l.set i a := by
  rw [mem_iff_getElem]
  grind

theorem mem_or_eq_of_mem_set : ∀ {l : List α} {i : Nat} {a b : α}, a ∈ l.set i b → a ∈ l ∨ a = b
  | _ :: _, 0, _, _, h => by grind
  | _ :: _, _+1, _, _, .head .. => by grind
  -- FIXME without the type annotation on `h` we get stuck on an unfolded `Mem`
  | _ :: l, n+1, a, _, .tail _ (h : a ∈ l.set n _) => by grind

/-! ### BEq -/

theorem reflBEq_iff [BEq α] : ReflBEq (List α) ↔ ReflBEq α := by
  constructor
  · intro h
    constructor
    intro a
    suffices ([a] == [a]) = true by
      simpa only [List.instBEq, List.beq, Bool.and_true]
    simp
  · intro h
    constructor
    intro l
    induction l with grind

theorem lawfulBEq_iff [BEq α] : LawfulBEq (List α) ↔ LawfulBEq α := by
  constructor
  · intro h
    have : ReflBEq α := reflBEq_iff.mp inferInstance
    constructor
    intro a b h
    apply singleton_inj.1
    apply eq_of_beq
    grind
  · intro h
    infer_instance

/-! ### isEqv -/

theorem isEqv_eq [DecidableEq α] {l₁ l₂ : List α} : l₁.isEqv l₂ (· == ·) = (l₁ = l₂) := by
  induction l₁ generalizing l₂ with grind [cases List]

/-! ### getLast -/

-- attribute [grind] List.length_pos_of_ne_nil  -- FIXME bad!

theorem getLast_eq_getElem : ∀ {l : List α} (h : l ≠ []),
    getLast l h = l[l.length - 1]'(by grind)
  | [_], _ => rfl -- FIXME by grind -- Can't see that [head].length - 1 = 0?
  | _ :: _ :: _, _ => by grind

theorem getLast_mem : ∀ {l : List α} (h : l ≠ []), getLast l h ∈ l
  | [], h => absurd rfl h
  | [_], _ => .head ..
  | _::a::l, _ => .tail _ <| getLast_mem (cons_ne_nil a l)

theorem getLast_mem_getLast? : ∀ {l : List α} (h : l ≠ []), getLast l h ∈ getLast? l
  | [], h => by contradiction
  | _ :: _, _ => rfl

theorem getLastD_mem_cons : ∀ {l : List α} {a : α}, getLastD l a ∈ a::l
  | [], _ => .head ..
  | _::_, _ => .tail _ <| getLast_mem _

/-! ### getLast! -/

theorem getLast!_of_getLast? [Inhabited α] : ∀ {l : List α}, getLast? l = some a → getLast! l = a
  | _ :: _, rfl => rfl

/-! ## Head and tail -/

/-! ### head -/

theorem head?_singleton {a : α} : head? [a] = some a := by grind

theorem head!_of_head? [Inhabited α] : ∀ {l : List α}, head? l = some a → head! l = a
  | _ :: _, rfl => rfl

theorem head?_eq_head : ∀ {l : List α} h, l.head? = some (head l h)
  | _ :: _, _ => rfl

theorem head_mem : ∀ {l : List α} (h : l ≠ []), head l h ∈ l
  | [], h => absurd rfl h
  | _::_, _ => .head ..

/-! ### tail -/

theorem tail_eq_tail? {l : List α} : l.tail = (tail? l).getD [] := by grind [tail_eq_tailD]

theorem head_tail {l : List α} (h : l.tail ≠ []) :
    (tail l).head h = l[1]'(one_lt_length_of_tail_ne_nil h) := by
  cases l with grind

theorem head?_tail {l : List α} : (tail l).head? = l[1]? := by
  grind [List.head?_eq_getElem?]

theorem getLast_tail {l : List α} (h : l.tail ≠ []) :
    (tail l).getLast h = l.getLast (ne_nil_of_tail_ne_nil h) := by grind

theorem getLast?_tail {l : List α} : (tail l).getLast? = if l.length = 1 then none else l.getLast? := by
  match l with
  | [] | [_] | _ :: _ :: _ => grind

/-! ## Basic operations -/

/-! ### map -/

-- FIXME work out how to get grind to do something useful here!
theorem getElem_map (f : α → β) {l} {i : Nat} {h : i < (map f l).length} :
    (map f l)[i] = f (l[i]'(length_map f ▸ h)) :=
  Option.some.inj <| by rw [← getElem?_eq_getElem, getElem?_map, getElem?_eq_getElem]; rfl

theorem exists_of_mem_map (h : b ∈ map f l) : ∃ a, a ∈ l ∧ f a = b := mem_map.1 h

theorem mem_map_of_mem {f : α → β} (h : a ∈ l) : f a ∈ map f l := mem_map.2 ⟨_, h, rfl⟩

theorem map_congr_left (h : ∀ a ∈ l, f a = g a) : map f l = map g l :=
  map_inj_left.2 h

theorem map_inj : map f = map g ↔ f = g := by
  constructor
  · intro h; ext a; replace h := congrFun h [a]; grind
  · grind

theorem tailD_map {f : α → β} {l l' : List α} :
    tailD (map f l) (map f l') = map f (tailD l l') := by simp [← map_tail?]

/-! ### filter -/

theorem filter_eq_nil_iff {l} : filter p l = [] ↔ ∀ a, a ∈ l → ¬p a := by
  simp only [eq_nil_iff_forall_not_mem, mem_filter, not_and]

theorem filter_eq_cons_iff {l} {a} {as} :
    filter p l = a :: as ↔
      ∃ l₁ l₂, l = l₁ ++ a :: l₂ ∧ (∀ x, x ∈ l₁ → ¬p x) ∧ p a ∧ filter p l₂ = as := by
  constructor
  · induction l with
    | nil => grind
    | cons x l ih =>
      intro h
      simp only [filter_cons] at h
      split at h <;> rename_i w
      · simp only [cons.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨[], l, by grind⟩
      · obtain ⟨l₁, l₂, rfl, w₁, w₂, w₃⟩ := ih h
        exact ⟨x :: l₁, l₂, by grind⟩
  · rintro ⟨l₁, l₂, rfl, h₁, h, h₂⟩
    have := filter_eq_nil_iff.mpr h₁
    grind

theorem filter_congr {p q : α → Bool} :
    ∀ {l : List α}, (∀ x ∈ l, p x = q x) → filter p l = filter q l
  | [], _ => rfl
  | a :: l, h => by
    rw [forall_mem_cons] at h; by_cases pa : p a
    · simp [pa, h.1 ▸ pa, filter_congr h.2]
    · simp [pa, h.1 ▸ pa, filter_congr h.2]

theorem filter_sublist {p : α → Bool} : ∀ {l : List α}, filter p l <+ l
  | [] => .slnil
  | a :: l => by
    rw [filter]
    split <;> simp [Sublist.cons, filter_sublist]

theorem filter_filterMap {f : α → Option β} {p : β → Bool} {l : List α} :
    filter p (filterMap f l) = filterMap (fun x => (f x).filter p) l := by
  rw [← filterMap_eq_filter]
  grind

theorem map_filterMap_of_inv
    {f : α → Option β} {g : β → α} (H : ∀ x : α, (f x).map g = some x) {l : List α} :
    map g (filterMap f l) = l := by simp only [map_filterMap, H, filterMap_some]

theorem forall_none_of_filterMap_eq_nil (h : filterMap f xs = []) : ∀ x ∈ xs, f x = none := by
  intro x hx
  induction xs with
  | nil => grind
  | cons y ys ih =>
    simp only [filterMap_cons] at h
    split at h
    · cases hx with
      | head => grind
      | tail _ hmem => exact ih h hmem -- FIXME hmem's type is broken
    · grind

theorem filterMap_eq_cons_iff {l} {b} {bs} :
    filterMap f l = b :: bs ↔
      ∃ l₁ a l₂, l = l₁ ++ a :: l₂ ∧ (∀ x, x ∈ l₁ → f x = none) ∧ f a = some b ∧
        filterMap f l₂ = bs := by
  constructor
  · induction l with
    | nil => grind
    | cons a l ih =>
      cases h : f a with
      | none =>
        simp only [filterMap_cons_none h]
        intro w
        specialize ih w
        obtain ⟨l₁, a', l₂, rfl, w₁, w₂, w₃⟩ := ih
        exact ⟨a :: l₁, a', l₂, by grind⟩
      | some b =>
        simp only [filterMap_cons_some h, cons.injEq, and_imp]
        rintro rfl rfl
        refine ⟨[], a, l, by grind⟩
  · rintro ⟨l₁, a, l₂, rfl, h₁, h₂, h₃⟩
    simp_all [filterMap_eq_nil_iff.mpr h₁, filterMap_cons_some h₂]

/-! ### append -/

theorem append_inj :
    ∀ {s₁ s₂ t₁ t₂ : List α}, s₁ ++ t₁ = s₂ ++ t₂ → length s₁ = length s₂ → s₁ = s₂ ∧ t₁ = t₂
  | [], [], _, _, h, _ => ⟨rfl, h⟩
  | _ :: _, _ :: _, _, _, h, hl => by
    simp [append_inj (cons.inj h).2 (Nat.succ.inj hl)] at h ⊢
    grind

theorem append_inj_right (h : s₁ ++ t₁ = s₂ ++ t₂) (hl : length s₁ = length s₂) : t₁ = t₂ :=
  (append_inj h hl).right

theorem append_inj_left (h : s₁ ++ t₁ = s₂ ++ t₂) (hl : length s₁ = length s₂) : s₁ = s₂ :=
  (append_inj h hl).left

/-- Variant of `append_inj` instead requiring equality of the lengths of the second lists. -/
theorem append_inj' (h : s₁ ++ t₁ = s₂ ++ t₂) (hl : length t₁ = length t₂) : s₁ = s₂ ∧ t₁ = t₂ :=
  append_inj h <| @Nat.add_right_cancel _ t₁.length _ <| by
    let hap := congrArg length h
    grind

/-- Variant of `append_inj_right` instead requiring equality of the lengths of the second lists. -/
theorem append_inj_right' (h : s₁ ++ t₁ = s₂ ++ t₂) (hl : length t₁ = length t₂) : t₁ = t₂ :=
  (append_inj' h hl).right

/-- Variant of `append_inj_left` instead requiring equality of the lengths of the second lists. -/
theorem append_inj_left' (h : s₁ ++ t₁ = s₂ ++ t₂) (hl : length t₁ = length t₂) : s₁ = s₂ :=
  (append_inj' h hl).left

theorem append_right_inj {t₁ t₂ : List α} (s) : s ++ t₁ = s ++ t₂ ↔ t₁ = t₂ :=
  ⟨fun h => append_inj_right h rfl, congrArg _⟩

theorem append_left_inj {s₁ s₂ : List α} (t) : s₁ ++ t = s₂ ++ t ↔ s₁ = s₂ :=
  ⟨fun h => append_inj_left' h rfl, congrArg (· ++ _)⟩

theorem append_left_eq_self {xs ys : List α} : xs ++ ys = ys ↔ xs = [] := by
  rw [← append_left_inj (s₁ := xs), nil_append]

theorem self_eq_append_left {xs ys : List α} : ys = xs ++ ys ↔ xs = [] := by
  rw [eq_comm, append_left_eq_self]

theorem append_right_eq_self {xs ys : List α} : xs ++ ys = xs ↔ ys = [] := by
  rw [← append_right_inj (t₁ := ys), append_nil]

theorem self_eq_append_right {xs ys : List α} : xs = xs ++ ys ↔ ys = [] := by
  rw [eq_comm, append_right_eq_self]

theorem append_eq_cons_iff :
    as ++ bs = x :: c ↔ (as = [] ∧ bs = x :: c) ∨ (∃ as', as = x :: as' ∧ c = as' ++ bs) := by
  cases as with simp | cons a as => ?_
  exact ⟨fun h => ⟨as, by grind⟩, fun ⟨as', ⟨aeq, aseq⟩, h⟩ => ⟨aeq, by grind⟩⟩

theorem filterMap_eq_append_iff {f : α → Option β} :
    filterMap f l = L₁ ++ L₂ ↔ ∃ l₁ l₂, l = l₁ ++ l₂ ∧ filterMap f l₁ = L₁ ∧ filterMap f l₂ = L₂ := by
  constructor
  · induction l generalizing L₁ with
    | nil =>
      simp only [filterMap_nil, nil_eq_append_iff, and_imp]
      rintro rfl rfl
      exact ⟨[], [], by simp⟩
    | cons x l ih =>
      simp only [filterMap_cons]
      split
      · intro h
        obtain ⟨l₁, l₂, rfl, rfl, rfl⟩ := ih h
        refine ⟨x :: l₁, l₂, ?_⟩
        grind
      · rename_i b w
        intro h
        rcases cons_eq_append_iff.mp h with (⟨rfl, rfl⟩ | ⟨_, ⟨rfl, h⟩⟩)
        · refine ⟨[], x :: l, ?_⟩
          grind
        · obtain ⟨l₁, l₂, rfl, rfl, rfl⟩ := ih ‹_›
          refine ⟨x :: l₁, l₂, ?_⟩
          grind
  · grind

theorem filter_eq_append_iff {p : α → Bool} :
    filter p l = L₁ ++ L₂ ↔ ∃ l₁ l₂, l = l₁ ++ l₂ ∧ filter p l₁ = L₁ ∧ filter p l₂ = L₂ := by
  rw [← filterMap_eq_filter, filterMap_eq_append_iff]

theorem map_eq_append_iff {f : α → β} :
    map f l = L₁ ++ L₂ ↔ ∃ l₁ l₂, l = l₁ ++ l₂ ∧ map f l₁ = L₁ ∧ map f l₂ = L₂ := by
  rw [← filterMap_eq_map, filterMap_eq_append_iff]

/-! ### concat
-/

-- As `List.concat` is defined in `Init.Prelude`, we write the basic simplification lemmas here.
theorem concat_nil {a : α} : concat [] a = [a] :=
  rfl
theorem concat_cons {a b : α} {l : List α} : concat (a :: l) b = a :: concat l b :=
  rfl

theorem init_eq_of_concat_eq {a b : α} {l₁ l₂ : List α} : concat l₁ a = concat l₂ b → l₁ = l₂ := by
  simp only [concat_eq_append]
  intro h
  apply append_inj_left' h (by simp)

theorem last_eq_of_concat_eq {a b : α} {l₁ l₂ : List α} : concat l₁ a = concat l₂ b → a = b := by
  simp only [concat_eq_append]
  intro h
  simpa using append_inj_right' h (by simp)

theorem concat_inj {a b : α} {l l' : List α} : concat l a = concat l' b ↔ l = l' ∧ a = b :=
  ⟨fun h => ⟨init_eq_of_concat_eq h, last_eq_of_concat_eq h⟩, by rintro ⟨rfl, rfl⟩; rfl⟩

theorem concat_inj_left {l l' : List α} (a : α) : concat l a = concat l' a ↔ l = l' :=
  ⟨init_eq_of_concat_eq, by simp⟩

theorem concat_inj_right {l : List α} {a a' : α} : concat l a = concat l a' ↔ a = a' :=
  ⟨last_eq_of_concat_eq, by simp⟩

theorem eq_nil_or_concat : ∀ l : List α, l = [] ∨ ∃ l' b, l = concat l' b
  | [] => .inl rfl
  | a::l => match l, eq_nil_or_concat l with
    | _, .inl rfl => .inr ⟨[], a, rfl⟩
    | _, .inr ⟨l', b, rfl⟩ => .inr ⟨a::l', b, rfl⟩

/-! ### flatten -/

theorem mem_flatten : ∀ {L : List (List α)}, a ∈ L.flatten ↔ ∃ l, l ∈ L ∧ a ∈ l
  | [] => by grind
  | _ :: _ => by grind [mem_flatten]

theorem flatten_eq_nil_iff {L : List (List α)} : L.flatten = [] ↔ ∀ l ∈ L, l = [] := by
  induction L with simp_all

theorem flatten_ne_nil_iff {xss : List (List α)} : xss.flatten ≠ [] ↔ ∃ xs, xs ∈ xss ∧ xs ≠ [] := by
  simp

theorem exists_of_mem_flatten : a ∈ flatten L → ∃ l, l ∈ L ∧ a ∈ l := mem_flatten.1

theorem mem_flatten_of_mem (lL : l ∈ L) (al : a ∈ l) : a ∈ flatten L := mem_flatten.2 ⟨l, lL, al⟩

theorem forall_mem_flatten {p : α → Prop} {L : List (List α)} :
    (∀ (x) (_ : x ∈ flatten L), p x) ↔ ∀ (l) (_ : l ∈ L) (x) (_ : x ∈ l), p x := by
  grind [mem_flatten]

theorem flatten_filter_not_isEmpty  :
    ∀ {L : List (List α)}, flatten (L.filter fun l => !l.isEmpty) = L.flatten
  | [] => by grind
  | [] :: L
  | (a :: l) :: L => by
    simp [flatten_filter_not_isEmpty (L := L)]

theorem flatten_filter_ne_nil [DecidablePred fun l : List α => l ≠ []] {L : List (List α)} :
    flatten (L.filter fun l => l ≠ []) = L.flatten := by
  grind [flatten_filter_not_isEmpty]

theorem flatten_eq_cons_iff {xss : List (List α)} {y : α} {ys : List α} :
    xss.flatten = y :: ys ↔
      ∃ as bs cs, xss = as ++ (y :: bs) :: cs ∧ (∀ l, l ∈ as → l = []) ∧ ys = bs ++ cs.flatten := by
  constructor
  · induction xss with
    | nil => grind
    | cons xs xss ih =>
      intro h
      simp only [flatten_cons] at h
      replace h := h.symm
      rw [cons_eq_append_iff] at h
      obtain (⟨rfl, h⟩ | ⟨z⟩) := h
      · obtain ⟨as, bs, cs, rfl, _, rfl⟩ := ih h
        exact ⟨[] :: as, bs, cs, by grind⟩
      · obtain ⟨as', rfl, rfl⟩ := z
        exact ⟨[], as', xss, by grind⟩
  · rintro ⟨as, bs, cs, rfl, h₁, rfl⟩
    grind [flatten_eq_nil_iff]

theorem cons_eq_flatten_iff {xs : List (List α)} {y : α} {ys : List α} :
    y :: ys = xs.flatten ↔
      ∃ as bs cs, xs = as ++ (y :: bs) :: cs ∧ (∀ l, l ∈ as → l = []) ∧ ys = bs ++ cs.flatten := by
  grind [flatten_eq_cons_iff]

theorem flatten_eq_singleton_iff {xs : List (List α)} {y : α} :
    xs.flatten = [y] ↔ ∃ as bs, xs = as ++ [y] :: bs ∧ (∀ l, l ∈ as → l = []) ∧ (∀ l, l ∈ bs → l = []) := by
  rw [flatten_eq_cons_iff]
  constructor
  · rintro ⟨as, bs, cs, rfl, h₁, h₂⟩
    simp at h₂
    obtain ⟨rfl, h₂⟩ := h₂
    exact ⟨as, cs, by grind, h₁, h₂⟩
  · rintro ⟨as, bs, rfl, h₁, h₂⟩
    exact ⟨as, [], bs, rfl, h₁, by simpa⟩

theorem flatten_eq_append_iff {xss : List (List α)} {ys zs : List α} :
    xss.flatten = ys ++ zs ↔
      (∃ as bs, xss = as ++ bs ∧ ys = as.flatten ∧ zs = bs.flatten) ∨
        ∃ as bs c cs ds, xss = as ++ (bs ++ c :: cs) :: ds ∧ ys = as.flatten ++ bs ∧
          zs = c :: cs ++ ds.flatten := by
  constructor
  · induction xss generalizing ys with
    | nil =>
      simp only [flatten_nil, nil_eq, append_eq_nil_iff, and_false, cons_append, false_and,
        exists_const, exists_false, or_false, and_imp, List.cons_ne_nil]
      rintro rfl rfl
      exact ⟨[], [], by grind⟩
    | cons xs xss ih =>
      intro h
      simp only [flatten_cons] at h
      rw [append_eq_append_iff] at h
      obtain (⟨ys, rfl, h⟩ | ⟨bs, rfl, h⟩) := h
      · obtain (⟨as, bs, rfl, rfl, rfl⟩ | ⟨as, bs, c, cs, ds, rfl, rfl, rfl⟩) := ih h
        · exact .inl ⟨xs :: as, bs, by grind⟩
        · exact .inr ⟨xs :: as, bs, c, cs, ds, by grind⟩
      · simp only [h]
        cases bs with
        | nil => exact .inl ⟨[ys], xss, by grind⟩
        | cons b bs => exact .inr ⟨[], ys, b, bs, xss, by grind⟩
  · grind


/-- Two lists of sublists are equal iff their flattens coincide, as well as the lengths of the
sublists. -/
theorem eq_iff_flatten_eq : ∀ {L L' : List (List α)},
    L = L' ↔ L.flatten = L'.flatten ∧ map length L = map length L'
  | _, [] => by simp_all
  | [], _ :: _ => by simp_all
  | _ :: _, _ :: _ => by
    simp only [cons.injEq, flatten_cons, map_cons]
    rw [eq_iff_flatten_eq]
    constructor
    · grind
    · rintro ⟨h₁, h₂, h₃⟩
      obtain ⟨rfl, h⟩ := append_inj h₁ h₂
      grind

/-! ### flatMap -/

theorem flatMap_def {l : List α} {f : α → List β} : l.flatMap f = flatten (map f l) := by rfl

theorem flatMap_id {L : List (List α)} : L.flatMap id = L.flatten := by simp [flatMap_def]

theorem flatMap_id' {L : List (List α)} : L.flatMap (fun as => as) = L.flatten := by simp [flatMap_def]

theorem length_flatMap {l : List α} {f : α → List β} :
    length (l.flatMap f) = sum (map (fun a => (f a).length) l) := by
  grind [Function.comp_def]

theorem mem_flatMap {f : α → List β} {b} {l : List α} : b ∈ l.flatMap f ↔ ∃ a, a ∈ l ∧ b ∈ f a := by
  simp [flatMap_def]
  exact ⟨fun ⟨_, ⟨a, h₁, rfl⟩, h₂⟩ => ⟨a, h₁, h₂⟩, fun ⟨a, h₁, h₂⟩ => ⟨_, ⟨a, h₁, rfl⟩, h₂⟩⟩

-- attribute [grind] List.mem_map

theorem flatMap_eq_nil_iff {l : List α} {f : α → List β} : l.flatMap f = [] ↔ ∀ x ∈ l, f x = [] :=
  flatten_eq_nil_iff.trans <| by
    simp only [mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]

theorem map_flatMap {f : β → γ} {g : α → List β} :
    ∀ {l : List α}, (l.flatMap g).map f = l.flatMap fun a => (g a).map f
  | [] => rfl
  | a::l => by simp only [flatMap_cons, map_append, map_flatMap]

theorem map_eq_flatMap {f : α → β} {l : List α} : map f l = l.flatMap fun x => [f x] := by
  simp only [← map_singleton]
  rw [← flatMap_singleton' l, map_flatMap, flatMap_singleton']

/-! ### replicate -/

theorem getElem_replicate {a : α} {n : Nat} {i : Nat} (h : i < (replicate n a).length) :
    (replicate n a)[i] = a :=
  eq_of_mem_replicate (getElem_mem _)

theorem replicate_inj : replicate n a = replicate m b ↔ n = m ∧ (n = 0 ∨ a = b) :=
  ⟨fun h => have eq : n = m := by simpa using congrArg length h
    ⟨eq, by
    by_cases w : n = 0
    · grind
    · have p := congrArg (·[0]?) h
      grind⟩,
    by grind⟩

theorem eq_replicate_of_mem {a : α} :
    ∀ {l : List α}, (∀ (b) (_ : b ∈ l), b = a) → l = replicate l.length a
  | [], _ => rfl
  | b :: l, H => by
    let ⟨rfl, H₂⟩ := forall_mem_cons (l := l).1 H
    rw [length_cons, replicate, ← eq_replicate_of_mem H₂]

theorem eq_replicate_iff {a : α} {n} {l : List α} :
    l = replicate n a ↔ length l = n ∧ ∀ (b) (_ : b ∈ l), b = a :=
  ⟨fun h => h ▸ ⟨length_replicate .., fun _ => eq_of_mem_replicate⟩,
   fun ⟨e, al⟩ => e ▸ eq_replicate_of_mem al⟩

theorem map_eq_replicate_iff {l : List α} {f : α → β} {b : β} :
    l.map f = replicate l.length b ↔ ∀ x ∈ l, f x = b := by
  simp [eq_replicate_iff]

theorem map_const {l : List α} {b : β} : map (Function.const α b) l = replicate l.length b :=
  map_eq_replicate_iff.mpr fun _ _ => rfl

theorem map_const_fun {x : β} : map (Function.const α x) = (replicate ·.length x) := by
  funext l
  simp

theorem map_const' {l : List α} {b : β} : map (fun _ => b) l = replicate l.length b :=
  map_const

theorem append_eq_replicate_iff {l₁ l₂ : List α} {a : α} :
    l₁ ++ l₂ = replicate n a ↔
      l₁.length + l₂.length = n ∧ l₁ = replicate l₁.length a ∧ l₂ = replicate l₂.length a := by
  simp only [eq_replicate_iff, length_append, mem_append, true_and, and_congr_right_iff]
  exact fun _ =>
    { mp := fun h => ⟨fun b m => h b (Or.inl m), fun b m => h b (Or.inr m)⟩,
      mpr := fun h b x => Or.casesOn x (fun m => h.left b m) fun m => h.right b m }

theorem filterMap_replicate_of_some {f : α → Option β} (h : f a = some b) :
    (replicate n a).filterMap f = replicate n b := by
  simp [h]

theorem filterMap_replicate_of_isSome {f : α → Option β} (h : (f a).isSome) :
    (replicate n a).filterMap f = replicate n (Option.get _ h) := by
  rw [Option.isSome_iff_exists] at h
  obtain ⟨b, h⟩ := h
  simp [h]

theorem filterMap_replicate_of_none {f : α → Option β} (h : f a = none) :
    (replicate n a).filterMap f = [] := by
  simp [h]

theorem flatten_replicate_replicate : (replicate n (replicate m a)).flatten = replicate (n * m) a := by
  induction n with
  | zero => grind
  | succ n ih =>
    simp only [replicate_succ, flatten_cons, ih, replicate_append_replicate,
      add_one_mul, Nat.add_comm]

theorem eq_replicate_or_eq_replicate_append_cons {α : Type _} (l : List α) :
    (l = []) ∨ (∃ n a, l = replicate n a ∧ 0 < n) ∨
      (∃ n a b l', l = replicate n a ++ b :: l' ∧ 0 < n ∧ a ≠ b) := by
  induction l with
  | nil => grind
  | cons x l ih =>
    right
    rcases ih with rfl | ⟨n, a, rfl, h⟩ | ⟨n, a, b, l', rfl, h⟩
    · left
      exact ⟨1, x, rfl, by grind⟩
    · by_cases h' : x = a
      · subst h'
        left
        exact ⟨n + 1, x, rfl, by grind⟩
      · right
        refine ⟨1, x, a, replicate (n - 1) a, ?_, by grind, h'⟩
        match n with | n + 1 => grind
    · right
      by_cases h' : x = a
      · subst h'
        refine ⟨n + 1, x, b, l', by grind, by simp, h.2⟩
      · refine ⟨1, x, a, replicate (n - 1) a ++ b :: l', ?_, by grind, h'⟩
        match n with | n + 1 => grind

theorem replicateRecOn {α : Type _} {p : List α → Prop} (l : List α)
    (h0 : p []) (hr : ∀ a n, 0 < n → p (replicate n a))
    (hi : ∀ a b n l, a ≠ b → 0 < n → p (b :: l) → p (replicate n a ++ b :: l)) : p l := by
  rcases eq_replicate_or_eq_replicate_append_cons l with
    rfl | ⟨n, a, rfl, hn⟩ | ⟨n, a, b, l', w, hn, h⟩
  · exact h0
  · exact hr _ _ hn
  · have : (b :: l').length < l.length := by grind
    subst w
    exact hi _ _ _ _ h hn (replicateRecOn (b :: l') h0 hr hi)
termination_by l.length

/-! ### reverse -/

theorem mem_reverseAux {x : α} : ∀ {as bs}, x ∈ reverseAux as bs ↔ x ∈ as ∨ x ∈ bs
  | [], _ => ⟨.inr, fun | .inr h => h⟩
  | a :: _, _ => by rw [reverseAux, mem_cons, or_assoc, or_left_comm, mem_reverseAux, mem_cons]

-- The argument `as : List α` is explicit to allow rewriting from right to left.
theorem reverse_reverse (as : List α) : as.reverse.reverse = as := by
  simp only [reverse]; rw [reverseAux_reverseAux_nil]; rfl

theorem reverse_inj {xs ys : List α} : xs.reverse = ys.reverse ↔ xs = ys := by
  simp [reverse_eq_iff]

theorem reverse_eq_cons_iff {xs : List α} {a : α} {ys : List α} :
    xs.reverse = a :: ys ↔ xs = ys.reverse ++ [a] := by
  grind [reverse_cons]

theorem reverseAux_eq {as bs : List α} : reverseAux as bs = reverse as ++ bs :=
  reverseAux_eq_append ..

theorem reverse_replicate {n : Nat} {a : α} : reverse (replicate n a) = replicate n a :=
  eq_replicate_iff.2 (by grind)


/-! ### foldlM and foldrM -/

theorem foldlM_append [Monad m] [LawfulMonad m] {f : β → α → m β} {b : β} {l l' : List α} :
    (l ++ l').foldlM f b = l.foldlM f b >>= l'.foldlM f := by
  induction l generalizing b <;> simp [*]

theorem foldrM_cons [Monad m] [LawfulMonad m] {a : α} {l : List α} {f : α → β → m β} {b : β} :
    (a :: l).foldrM f b = l.foldrM f b >>= f a := by
  simp only [foldrM]
  induction l <;> simp_all

theorem id_run_foldlM {f : β → α → Id β} {b : β} {l : List α} :
    Id.run (l.foldlM f b) = l.foldl f b := foldl_eq_foldlM.symm

theorem id_run_foldrM {f : α → β → Id β} {b : β} {l : List α} :
    Id.run (l.foldrM f b) = l.foldr f b := foldr_eq_foldrM.symm

theorem foldlM_reverse [Monad m] {l : List α} {f : β → α → m β} {b : β} :
    l.reverse.foldlM f b = l.foldrM (fun x y => f y x) b := rfl

theorem foldrM_reverse [Monad m] {l : List α} {f : α → β → m β} {b : β} :
    l.reverse.foldrM f b = l.foldlM (fun x y => f y x) b :=
  (foldlM_reverse ..).symm.trans <| by grind

/-! ### foldl and foldr -/

theorem foldrM_append [Monad m] [LawfulMonad m] {f : α → β → m β} {b : β} {l l' : List α} :
    (l ++ l').foldrM f b = l'.foldrM f b >>= l.foldrM f := by
  induction l <;> simp [*]

theorem foldr_reverse {l : List α} {f : α → β → β} {b : β} :
    l.reverse.foldr f b = l.foldl (fun x y => f y x) b :=
  (foldl_reverse ..).symm.trans <| by grind

theorem foldr_assoc {op : α → α → α} [ha : Std.Associative op]
    {l : List α} {a₁ a₂} : l.foldr op (op a₁ a₂) = op (l.foldr op a₁) a₂ := by
  induction l generalizing a₁ a₂ <;> simp [*, ha.assoc]

def foldlRecOn {motive : β → Sort _} : ∀ (l : List α) (op : β → α → β) {b : β} (_ : motive b)
    (_ : ∀ (b : β) (_ : motive b) (a : α) (_ : a ∈ l), motive (op b a)), motive (List.foldl op b l)
  | [], _, _, hb, _ => hb
  | hd :: tl, op, b, hb, hl =>
    foldlRecOn tl op (hl b hb hd (by grind))
      fun y hy x hx => hl y hy x (by grind)

theorem foldlRecOn_nil {motive : β → Sort _} {op : β → α → β} (hb : motive b)
    (hl : ∀ (b : β) (_ : motive b) (a : α) (_ : a ∈ []), motive (op b a)) :
    foldlRecOn [] op hb hl = hb := rfl

theorem foldlRecOn_cons {motive : β → Sort _} {op : β → α → β} (hb : motive b)
    (hl : ∀ (b : β) (_ : motive b) (a : α) (_ : a ∈ x :: l), motive (op b a)) :
    foldlRecOn (x :: l) op hb hl =
      foldlRecOn l op (hl b hb x (by grind))
        (fun b c a m => hl b c a (by grind)) :=
  rfl

def foldrRecOn {motive : β → Sort _} : ∀ (l : List α) (op : α → β → β) {b : β} (_ : motive b)
    (_ : ∀ (b : β) (_ : motive b) (a : α) (_ : a ∈ l), motive (op a b)), motive (List.foldr op b l)
  | nil, _, _, hb, _ => hb
  | x :: l, op, b, hb, hl =>
    hl (foldr op b l)
      (foldrRecOn l op hb fun b c a m => hl b c a (by grind)) x (by grind)

theorem foldrRecOn_nil {motive : β → Sort _} {op : α → β → β} (hb : motive b)
    (hl : ∀ (b : β) (_ : motive b) (a : α) (_ : a ∈ []), motive (op a b)) :
    foldrRecOn [] op hb hl = hb := rfl

theorem foldrRecOn_cons {motive : β → Sort _} {op : α → β → β} (hb : motive b)
    (hl : ∀ (b : β) (_ : motive b) (a : α) (_ : a ∈ x :: l), motive (op a b)) :
    foldrRecOn (x :: l) op hb hl =
      hl _ (foldrRecOn l op hb fun b c a m => hl b c a (by grind))
        x (by grind) :=
  rfl

/-! #### Further results about `getLast` and `getLast?` -/

theorem getLast?_eq_none_iff {xs : List α} : xs.getLast? = none ↔ xs = [] := by
  rw [getLast?_eq_head?_reverse, head?_eq_none_iff, reverse_eq_nil_iff]

theorem getLast?_eq_some_iff {xs : List α} {a : α} : xs.getLast? = some a ↔ ∃ ys, xs = ys ++ [a] := by
  rw [getLast?_eq_head?_reverse, head?_eq_some_iff]
  simp only [reverse_eq_cons_iff]
  exact ⟨fun ⟨ys, h⟩ => ⟨ys.reverse, by simpa using h⟩, fun ⟨ys, h⟩ => ⟨ys.reverse, by simpa using h⟩⟩

theorem getLast?_isSome : l.getLast?.isSome ↔ l ≠ [] := by
  rw [getLast?_eq_head?_reverse, isSome_head?]
  simp

-- attribute [grind] List.head_filter_of_pos

-- theorem getLast_filter_of_pos {p : α → Bool} {l : List α} (w : l ≠ []) (h : p (getLast l w) = true) :
--     getLast (filter p l) (ne_nil_of_mem (mem_filter.2 ⟨getLast_mem w, by grind⟩)) = getLast l w := by grind [head_filter_of_pos]

-- attribute [grind] List.head_filterMap_of_eq_some

-- theorem getLast_filterMap_of_eq_some {f : α → Option β} {l : List α} (w : l ≠ []) {b : β} (h : f (l.getLast w) = some b) :
--     (filterMap f l).getLast (ne_nil_of_mem (mem_filterMap.2 ⟨_, getLast_mem w, h⟩)) = b := by grind


-- attribute [grind] List.getLast?_eq_head?_reverse List.head?_eq_getLast?_reverse

-- theorem getLast?_flatMap {l : List α} {f : α → List β} :
--     (l.flatMap f).getLast? = l.reverse.findSome? fun a => (f a).getLast? := by
--   grind


-- theorem getLast?_flatten {L : List (List α)} :
--     (flatten L).getLast? = L.reverse.findSome? fun l => l.getLast? := by
--   grind?

/-! ## Additional operations -/



/-! ## List membership -/

/-! ## Sublists -/

/-! ### partition

Because we immediately simplify `partition` into two `filter`s for verification purposes,
we do not separately develop much theory about it.
-/

theorem partition_eq_filter_filter {p : α → Bool} {l : List α} :
    partition p l = (filter p l, filter (not ∘ p) l) := by simp [partition, aux]
  where
    aux l {as bs} : partition.loop p l (as, bs) =
        (as.reverse ++ filter p l, bs.reverse ++ filter (not ∘ p) l) := by
      induction l generalizing as bs with
      | nil => grind [partition.loop]
      | cons a l ih => cases pa : p a <;> grind [partition.loop]

/-! ### dropLast

`dropLast` is the specification for `Array.pop`, so theorems about `List.dropLast`
are often used for theorems about `Array.pop`.
-/



theorem dropLast_cons_of_ne_nil {α : Type u} {x : α}
    {l : List α} (h : l ≠ []) : (x :: l).dropLast = x :: l.dropLast := by
  grind [dropLast]

theorem dropLast_concat_getLast : ∀ {l : List α} (h : l ≠ []), dropLast l ++ [getLast l h] = l
  | [], h => absurd rfl h
  | [_], _ => rfl
  | _ :: b :: l, _ => by
    rw [dropLast_cons₂, cons_append, getLast_cons (cons_ne_nil _ _)]
    congr
    exact dropLast_concat_getLast (cons_ne_nil b l)

theorem dropLast_append_of_ne_nil {α : Type u} {l : List α} :
    ∀ {l' : List α} (_ : l ≠ []), (l' ++ l).dropLast = l' ++ l.dropLast
  | [], _ => by simp only [nil_append]
  | a :: l', h => by
    rw [cons_append, dropLast, dropLast_append_of_ne_nil h, cons_append]
    simp [h]

theorem dropLast_cons_self_replicate {n : Nat} {a : α} :
    dropLast (a :: replicate n a) = replicate n a := by
  rw [← replicate_succ, dropLast_replicate, Nat.add_sub_cancel]

theorem tail_reverse {l : List α} : l.reverse.tail = l.dropLast.reverse := by
  apply ext_getElem <;> grind

/-!
### splitAt
-/

theorem splitAt_go {i : Nat} {l acc : List α} :
    splitAt.go l xs i acc =
      if i < xs.length then (acc.reverse ++ xs.take i, xs.drop i) else (l, []) := by
  induction xs generalizing i acc with
  | nil => simp [splitAt.go]
  | cons x xs ih =>
    cases i with
    | zero => simp [splitAt.go]
    | succ i => grind [splitAt.go]

/-! ## Manipulating elements -/

/-! ### replace -/
section replace
variable [BEq α]

theorem head_replace {l : List α} {a b : α} (w) :
    (l.replace a b).head w =
      if a == l.head (by rintro rfl; simp_all) then
        b
      else
        l.head  (by rintro rfl; simp_all) := by
  apply Option.some.inj
  rw [← head?_eq_head, head?_replace, head?_eq_head]

theorem replace_replicate_ne [LawfulBEq α] {a b c : α} (h : !b == a) :
    (replicate n a).replace b c = replicate n a := by
  grind [replace_of_not_mem]

end replace

/-! ### insert -/

section insert
variable [BEq α]

variable [LawfulBEq α]

theorem head?_insert {l : List α} {a : α} :
    (l.insert a).head? = some (if h : a ∈ l then l.head (ne_nil_of_mem h) else a) := by
  simp only [insert_eq]
  split <;> rename_i h
  · simp [head?_eq_head (ne_nil_of_mem h)]
  · grind

theorem head_insert {l : List α} {a : α} (w) :
    (l.insert a).head w = if h : a ∈ l then l.head (ne_nil_of_mem h) else a := by
  apply Option.some.inj
  rw [← head?_eq_head, head?_insert]

end insert

end List'

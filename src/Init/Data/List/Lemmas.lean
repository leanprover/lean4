/-
Copyright (c) 2014 Parikshit Khanna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Parikshit Khanna, Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Mario Carneiro
-/
prelude
import Init.Data.List.BasicAux
import Init.Data.List.Control
import Init.PropLemmas
import Init.Control.Lawful.Basic
import Init.Hints

namespace List

open Nat

/-!
# Bootstrapping theorems for lists

These are theorems used in the definitions of `Std.Data.List.Basic` and tactics.
New theorems should be added to `Std.Data.List.Lemmas` if they are not needed by the bootstrap.
-/

attribute [simp] concat_eq_append append_assoc

@[simp] theorem get?_nil : @get? α [] n = none := rfl
@[simp] theorem get?_cons_zero : @get? α (a::l) 0 = some a := rfl
@[simp] theorem get?_cons_succ : @get? α (a::l) (n+1) = get? l n := rfl
@[simp] theorem get_cons_zero : get (a::l) (0 : Fin (l.length + 1)) = a := rfl
@[simp] theorem head?_nil : @head? α [] = none := rfl
@[simp] theorem head?_cons : @head? α (a::l) = some a := rfl
@[simp 1100] theorem headD_nil : @headD α [] d = d := rfl
@[simp 1100] theorem headD_cons : @headD α (a::l) d = a := rfl
@[simp] theorem head_cons : @head α (a::l) h = a := rfl
@[simp] theorem tail?_nil : @tail? α [] = none := rfl
@[simp] theorem tail?_cons : @tail? α (a::l) = some l := rfl
@[simp] theorem tail!_cons : @tail! α (a::l) = l := rfl
@[simp 1100] theorem tailD_nil : @tailD α [] l' = l' := rfl
@[simp 1100] theorem tailD_cons : @tailD α (a::l) l' = l := rfl
@[simp] theorem any_nil : [].any f = false := rfl
@[simp] theorem any_cons : (a::l).any f = (f a || l.any f) := rfl
@[simp] theorem all_nil : [].all f = true := rfl
@[simp] theorem all_cons : (a::l).all f = (f a && l.all f) := rfl
@[simp] theorem or_nil : [].or = false := rfl
@[simp] theorem or_cons : (a::l).or = (a || l.or) := rfl
@[simp] theorem and_nil : [].and = true := rfl
@[simp] theorem and_cons : (a::l).and = (a && l.and) := rfl

/-! ### length -/

theorem eq_nil_of_length_eq_zero (_ : length l = 0) : l = [] := match l with | [] => rfl

theorem ne_nil_of_length_eq_succ (_ : length l = succ n) : l ≠ [] := fun _ => nomatch l

theorem length_eq_zero : length l = 0 ↔ l = [] :=
  ⟨eq_nil_of_length_eq_zero, fun h => h ▸ rfl⟩

/-! ### mem -/

@[simp] theorem not_mem_nil (a : α) : ¬ a ∈ [] := nofun

@[simp] theorem mem_cons : a ∈ (b :: l) ↔ a = b ∨ a ∈ l :=
  ⟨fun h => by cases h <;> simp [Membership.mem, *],
   fun | Or.inl rfl => by constructor | Or.inr h => by constructor; assumption⟩

theorem mem_cons_self (a : α) (l : List α) : a ∈ a :: l := .head ..

theorem mem_cons_of_mem (y : α) {a : α} {l : List α} : a ∈ l → a ∈ y :: l := .tail _

theorem eq_nil_iff_forall_not_mem {l : List α} : l = [] ↔ ∀ a, a ∉ l := by
  cases l <;> simp [-not_or]

/-! ### append -/

@[simp 1100] theorem singleton_append : [x] ++ l = x :: l := rfl

theorem append_inj :
    ∀ {s₁ s₂ t₁ t₂ : List α}, s₁ ++ t₁ = s₂ ++ t₂ → length s₁ = length s₂ → s₁ = s₂ ∧ t₁ = t₂
  | [], [], t₁, t₂, h, _ => ⟨rfl, h⟩
  | a :: s₁, b :: s₂, t₁, t₂, h, hl => by
    simp [append_inj (cons.inj h).2 (Nat.succ.inj hl)] at h ⊢; exact h

theorem append_inj_right (h : s₁ ++ t₁ = s₂ ++ t₂) (hl : length s₁ = length s₂) : t₁ = t₂ :=
  (append_inj h hl).right

theorem append_inj_left (h : s₁ ++ t₁ = s₂ ++ t₂) (hl : length s₁ = length s₂) : s₁ = s₂ :=
  (append_inj h hl).left

theorem append_inj' (h : s₁ ++ t₁ = s₂ ++ t₂) (hl : length t₁ = length t₂) : s₁ = s₂ ∧ t₁ = t₂ :=
  append_inj h <| @Nat.add_right_cancel _ (length t₁) _ <| by
  let hap := congrArg length h; simp only [length_append, ← hl] at hap; exact hap

theorem append_inj_right' (h : s₁ ++ t₁ = s₂ ++ t₂) (hl : length t₁ = length t₂) : t₁ = t₂ :=
  (append_inj' h hl).right

theorem append_inj_left' (h : s₁ ++ t₁ = s₂ ++ t₂) (hl : length t₁ = length t₂) : s₁ = s₂ :=
  (append_inj' h hl).left

theorem append_right_inj {t₁ t₂ : List α} (s) : s ++ t₁ = s ++ t₂ ↔ t₁ = t₂ :=
  ⟨fun h => append_inj_right h rfl, congrArg _⟩

theorem append_left_inj {s₁ s₂ : List α} (t) : s₁ ++ t = s₂ ++ t ↔ s₁ = s₂ :=
  ⟨fun h => append_inj_left' h rfl, congrArg (· ++ _)⟩

@[simp] theorem append_eq_nil : p ++ q = [] ↔ p = [] ∧ q = [] := by
  cases p <;> simp

theorem get_append : ∀ {l₁ l₂ : List α} (n : Nat) (h : n < l₁.length),
    (l₁ ++ l₂).get ⟨n, length_append .. ▸ Nat.lt_add_right _ h⟩ = l₁.get ⟨n, h⟩
| a :: l, _, 0, h => rfl
| a :: l, _, n+1, h => by simp only [get, cons_append]; apply get_append

/-! ### map -/

@[simp] theorem map_nil {f : α → β} : map f [] = [] := rfl

@[simp] theorem map_cons (f : α → β) a l : map f (a :: l) = f a :: map f l := rfl

@[simp] theorem map_append (f : α → β) : ∀ l₁ l₂, map f (l₁ ++ l₂) = map f l₁ ++ map f l₂ := by
  intro l₁; induction l₁ <;> intros <;> simp_all

@[simp] theorem map_id (l : List α) : map id l = l := by induction l <;> simp_all

@[simp] theorem map_id' (l : List α) : map (fun a => a) l = l := by induction l <;> simp_all

@[simp] theorem mem_map {f : α → β} : ∀ {l : List α}, b ∈ l.map f ↔ ∃ a, a ∈ l ∧ f a = b
  | [] => by simp
  | _ :: l => by simp [mem_map (l := l), eq_comm (a := b)]

theorem mem_map_of_mem (f : α → β) (h : a ∈ l) : f a ∈ map f l := mem_map.2 ⟨_, h, rfl⟩

@[simp] theorem map_map (g : β → γ) (f : α → β) (l : List α) :
  map g (map f l) = map (g ∘ f) l := by induction l <;> simp_all

/-! ### bind -/

@[simp] theorem nil_bind (f : α → List β) : List.bind [] f = [] := by simp [join, List.bind]

@[simp] theorem cons_bind x xs (f : α → List β) :
  List.bind (x :: xs) f = f x ++ List.bind xs f := by simp [join, List.bind]

@[simp] theorem append_bind xs ys (f : α → List β) :
  List.bind (xs ++ ys) f = List.bind xs f ++ List.bind ys f := by
  induction xs; {rfl}; simp_all [cons_bind, append_assoc]

@[simp] theorem bind_id (l : List (List α)) : List.bind l id = l.join := by simp [List.bind]

/-! ### join -/

@[simp] theorem join_nil : List.join ([] : List (List α)) = [] := rfl

@[simp] theorem join_cons : (l :: ls).join = l ++ ls.join := rfl

/-! ### bounded quantifiers over Lists -/

theorem forall_mem_cons {p : α → Prop} {a : α} {l : List α} :
    (∀ x, x ∈ a :: l → p x) ↔ p a ∧ ∀ x, x ∈ l → p x :=
  ⟨fun H => ⟨H _ (.head ..), fun _ h => H _ (.tail _ h)⟩,
   fun ⟨H₁, H₂⟩ _ => fun | .head .. => H₁ | .tail _ h => H₂ _ h⟩

/-! ### reverse -/

@[simp] theorem reverseAux_nil : reverseAux [] r = r := rfl
@[simp] theorem reverseAux_cons : reverseAux (a::l) r = reverseAux l (a::r) := rfl

theorem reverseAux_eq (as bs : List α) : reverseAux as bs = reverse as ++ bs :=
  reverseAux_eq_append ..

theorem reverse_map (f : α → β) (l : List α) : (l.map f).reverse = l.reverse.map f := by
  induction l <;> simp [*]

@[simp] theorem reverse_eq_nil_iff {xs : List α} : xs.reverse = [] ↔ xs = [] := by
  match xs with
  | [] => simp
  | x :: xs => simp

/-! ### nth element -/

theorem get_of_mem : ∀ {a} {l : List α}, a ∈ l → ∃ n, get l n = a
  | _, _ :: _, .head .. => ⟨⟨0, Nat.succ_pos _⟩, rfl⟩
  | _, _ :: _, .tail _ m => let ⟨⟨n, h⟩, e⟩ := get_of_mem m; ⟨⟨n+1, Nat.succ_lt_succ h⟩, e⟩

theorem get_mem : ∀ (l : List α) n h, get l ⟨n, h⟩ ∈ l
  | _ :: _, 0, _ => .head ..
  | _ :: l, _+1, _ => .tail _ (get_mem l ..)

theorem mem_iff_get {a} {l : List α} : a ∈ l ↔ ∃ n, get l n = a :=
  ⟨get_of_mem, fun ⟨_, e⟩ => e ▸ get_mem ..⟩

theorem get?_len_le : ∀ {l : List α} {n}, length l ≤ n → l.get? n = none
  | [], _, _ => rfl
  | _ :: l, _+1, h => get?_len_le (l := l) <| Nat.le_of_succ_le_succ h

theorem get?_eq_get : ∀ {l : List α} {n} (h : n < l.length), l.get? n = some (get l ⟨n, h⟩)
  | _ :: _, 0, _ => rfl
  | _ :: l, _+1, _ => get?_eq_get (l := l) _

theorem get?_eq_some : l.get? n = some a ↔ ∃ h, get l ⟨n, h⟩ = a :=
  ⟨fun e =>
    have : n < length l := Nat.gt_of_not_le fun hn => by cases get?_len_le hn ▸ e
    ⟨this, by rwa [get?_eq_get this, Option.some.injEq] at e⟩,
  fun ⟨h, e⟩ => e ▸ get?_eq_get _⟩

@[simp] theorem get?_eq_none : l.get? n = none ↔ length l ≤ n :=
  ⟨fun e => Nat.ge_of_not_lt (fun h' => by cases e ▸ get?_eq_some.2 ⟨h', rfl⟩), get?_len_le⟩

@[simp] theorem get?_map (f : α → β) : ∀ l n, (map f l).get? n = (l.get? n).map f
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: l, n+1 => get?_map f l n

theorem get?_append {l₁ l₂ : List α} {n : Nat} (hn : n < l₁.length) :
  (l₁ ++ l₂).get? n = l₁.get? n := by
  have hn' : n < (l₁ ++ l₂).length := Nat.lt_of_lt_of_le hn <|
    length_append .. ▸ Nat.le_add_right ..
  rw [get?_eq_get hn, get?_eq_get hn', get_append]

@[simp] theorem get?_concat_length : ∀ (l : List α) (a : α), (l ++ [a]).get? l.length = some a
  | [], a => rfl
  | b :: l, a => by rw [cons_append, length_cons]; simp only [get?, get?_concat_length]

theorem getLast_eq_get : ∀ (l : List α) (h : l ≠ []),
    getLast l h = l.get ⟨l.length - 1, by
      match l with
      | [] => contradiction
      | a :: l => exact Nat.le_refl _⟩
  | [a], h => rfl
  | a :: b :: l, h => by
    simp [getLast, get, Nat.succ_sub_succ, getLast_eq_get]

@[simp] theorem getLast?_nil : @getLast? α [] = none := rfl

theorem getLast?_eq_getLast : ∀ l h, @getLast? α l = some (getLast l h)
  | [], h => nomatch h rfl
  | _::_, _ => rfl

theorem getLast?_eq_get? : ∀ (l : List α), getLast? l = l.get? (l.length - 1)
  | [] => rfl
  | a::l => by rw [getLast?_eq_getLast (a::l) nofun, getLast_eq_get, get?_eq_get]

@[simp] theorem getLast?_concat (l : List α) : getLast? (l ++ [a]) = some a := by
  simp [getLast?_eq_get?, Nat.succ_sub_succ]

theorem getD_eq_get? : ∀ l n (a : α), getD l n a = (get? l n).getD a
  | [], _, _ => rfl
  | _a::_, 0, _ => rfl
  | _::l, _+1, _ => getD_eq_get? (l := l) ..

theorem get?_append_right : ∀ {l₁ l₂ : List α} {n : Nat}, l₁.length ≤ n →
  (l₁ ++ l₂).get? n = l₂.get? (n - l₁.length)
| [], _, n, _ => rfl
| a :: l, _, n+1, h₁ => by
  rw [cons_append]
  simp [Nat.succ_sub_succ_eq_sub, get?_append_right (Nat.lt_succ.1 h₁)]

theorem get?_reverse' : ∀ {l : List α} (i j), i + j + 1 = length l →
    get? l.reverse i = get? l j
  | [], _, _, _ => rfl
  | a::l, i, 0, h => by simp [Nat.succ.injEq] at h; simp [h, get?_append_right, Nat.succ.injEq]
  | a::l, i, j+1, h => by
    have := Nat.succ.inj h; simp at this ⊢
    rw [get?_append, get?_reverse' _ j this]
    rw [length_reverse, ← this]; apply Nat.lt_add_of_pos_right (Nat.succ_pos _)

theorem get?_reverse {l : List α} (i) (h : i < length l) :
    get? l.reverse i = get? l (l.length - 1 - i) :=
  get?_reverse' _ _ <| by
    rw [Nat.add_sub_of_le (Nat.le_sub_one_of_lt h),
      Nat.sub_add_cancel (Nat.lt_of_le_of_lt (Nat.zero_le _) h)]

@[simp] theorem getD_nil : getD [] n d = d := rfl

@[simp] theorem getD_cons_zero : getD (x :: xs) 0 d = x := rfl

@[simp] theorem getD_cons_succ : getD (x :: xs) (n + 1) d = getD xs n d := rfl

/-! ### take and drop -/

@[simp] theorem take_append_drop : ∀ (n : Nat) (l : List α), take n l ++ drop n l = l
  | 0, _ => rfl
  | _+1, [] => rfl
  | n+1, x :: xs => congrArg (cons x) <| take_append_drop n xs

@[simp] theorem length_drop : ∀ (i : Nat) (l : List α), length (drop i l) = length l - i
  | 0, _ => rfl
  | succ i, [] => Eq.symm (Nat.zero_sub (succ i))
  | succ i, x :: l => calc
    length (drop (succ i) (x :: l)) = length l - i := length_drop i l
    _ = succ (length l) - succ i := (Nat.succ_sub_succ_eq_sub (length l) i).symm

theorem drop_length_le {l : List α} (h : l.length ≤ i) : drop i l = [] :=
  length_eq_zero.1 (length_drop .. ▸ Nat.sub_eq_zero_of_le h)

theorem take_length_le {l : List α} (h : l.length ≤ i) : take i l = l := by
  have := take_append_drop i l
  rw [drop_length_le h, append_nil] at this; exact this

@[simp] theorem take_zero (l : List α) : l.take 0 = [] := rfl

@[simp] theorem take_nil : ([] : List α).take i = [] := by cases i <;> rfl

@[simp] theorem take_cons_succ : (a::as).take (i+1) = a :: as.take i := rfl

@[simp] theorem drop_zero (l : List α) : l.drop 0 = l := rfl

@[simp] theorem drop_succ_cons : (a :: l).drop (n + 1) = l.drop n := rfl

@[simp] theorem drop_length (l : List α) : drop l.length l = [] := drop_length_le (Nat.le_refl _)

@[simp] theorem take_length (l : List α) : take l.length l = l := take_length_le (Nat.le_refl _)

theorem take_concat_get (l : List α) (i : Nat) (h : i < l.length) :
    (l.take i).concat l[i] = l.take (i+1) :=
  Eq.symm <| (append_left_inj _).1 <| (take_append_drop (i+1) l).trans <| by
    rw [concat_eq_append, append_assoc, singleton_append, get_drop_eq_drop, take_append_drop]

theorem reverse_concat (l : List α) (a : α) : (l.concat a).reverse = a :: l.reverse := by
  rw [concat_eq_append, reverse_append]; rfl

/-! ### takeWhile and dropWhile -/

@[simp] theorem dropWhile_nil : ([] : List α).dropWhile p = [] := rfl

theorem dropWhile_cons :
    (x :: xs : List α).dropWhile p = if p x then xs.dropWhile p else x :: xs := by
  split <;> simp_all [dropWhile]

/-! ### foldlM and foldrM -/

@[simp] theorem foldlM_reverse [Monad m] (l : List α) (f : β → α → m β) (b) :
    l.reverse.foldlM f b = l.foldrM (fun x y => f y x) b := rfl

@[simp] theorem foldlM_nil [Monad m] (f : β → α → m β) (b) : [].foldlM f b = pure b := rfl

@[simp] theorem foldlM_cons [Monad m] (f : β → α → m β) (b) (a) (l : List α) :
    (a :: l).foldlM f b = f b a >>= l.foldlM f := by
  simp [List.foldlM]

@[simp] theorem foldlM_append [Monad m] [LawfulMonad m] (f : β → α → m β) (b) (l l' : List α) :
    (l ++ l').foldlM f b = l.foldlM f b >>= l'.foldlM f := by
  induction l generalizing b <;> simp [*]

@[simp] theorem foldrM_nil [Monad m] (f : α → β → m β) (b) : [].foldrM f b = pure b := rfl

@[simp] theorem foldrM_cons [Monad m] [LawfulMonad m] (a : α) (l) (f : α → β → m β) (b) :
    (a :: l).foldrM f b = l.foldrM f b >>= f a := by
  simp only [foldrM]
  induction l <;> simp_all

@[simp] theorem foldrM_reverse [Monad m] (l : List α) (f : α → β → m β) (b) :
    l.reverse.foldrM f b = l.foldlM (fun x y => f y x) b :=
  (foldlM_reverse ..).symm.trans <| by simp

theorem foldl_eq_foldlM (f : β → α → β) (b) (l : List α) :
    l.foldl f b = l.foldlM (m := Id) f b := by
  induction l generalizing b <;> simp [*, foldl]

theorem foldr_eq_foldrM (f : α → β → β) (b) (l : List α) :
    l.foldr f b = l.foldrM (m := Id) f b := by
  induction l <;> simp [*, foldr]

/-! ### foldl and foldr -/

@[simp] theorem foldl_reverse (l : List α) (f : β → α → β) (b) :
    l.reverse.foldl f b = l.foldr (fun x y => f y x) b := by simp [foldl_eq_foldlM, foldr_eq_foldrM]

@[simp] theorem foldr_reverse (l : List α) (f : α → β → β) (b) :
    l.reverse.foldr f b = l.foldl (fun x y => f y x) b :=
  (foldl_reverse ..).symm.trans <| by simp

@[simp] theorem foldrM_append [Monad m] [LawfulMonad m] (f : α → β → m β) (b) (l l' : List α) :
    (l ++ l').foldrM f b = l'.foldrM f b >>= l.foldrM f := by
  induction l <;> simp [*]

@[simp] theorem foldl_append {β : Type _} (f : β → α → β) (b) (l l' : List α) :
    (l ++ l').foldl f b = l'.foldl f (l.foldl f b) := by simp [foldl_eq_foldlM]

@[simp] theorem foldr_append (f : α → β → β) (b) (l l' : List α) :
    (l ++ l').foldr f b = l.foldr f (l'.foldr f b) := by simp [foldr_eq_foldrM]

@[simp] theorem foldl_nil : [].foldl f b = b := rfl

@[simp] theorem foldl_cons (l : List α) (b : β) : (a :: l).foldl f b = l.foldl f (f b a) := rfl

@[simp] theorem foldr_nil : [].foldr f b = b := rfl

@[simp] theorem foldr_cons (l : List α) : (a :: l).foldr f b = f a (l.foldr f b) := rfl

@[simp] theorem foldr_self_append (l : List α) : l.foldr cons l' = l ++ l' := by
  induction l <;> simp [*]

theorem foldr_self (l : List α) : l.foldr cons [] = l := by simp

/-! ### mapM -/

/-- Alternate (non-tail-recursive) form of mapM for proofs. -/
def mapM' [Monad m] (f : α → m β) : List α → m (List β)
  | [] => pure []
  | a :: l => return (← f a) :: (← l.mapM' f)

@[simp] theorem mapM'_nil [Monad m] {f : α → m β} : mapM' f [] = pure [] := rfl
@[simp] theorem mapM'_cons [Monad m] {f : α → m β} :
    mapM' f (a :: l) = return ((← f a) :: (← l.mapM' f)) :=
  rfl

theorem mapM'_eq_mapM [Monad m] [LawfulMonad m] (f : α → m β) (l : List α) :
    mapM' f l = mapM f l := by simp [go, mapM] where
  go : ∀ l acc, mapM.loop f l acc = return acc.reverse ++ (← mapM' f l)
    | [], acc => by simp [mapM.loop, mapM']
    | a::l, acc => by simp [go l, mapM.loop, mapM']

@[simp] theorem mapM_nil [Monad m] (f : α → m β) : [].mapM f = pure [] := rfl

@[simp] theorem mapM_cons [Monad m] [LawfulMonad m] (f : α → m β) :
    (a :: l).mapM f = (return (← f a) :: (← l.mapM f)) := by simp [← mapM'_eq_mapM, mapM']

@[simp] theorem mapM_append [Monad m] [LawfulMonad m] (f : α → m β) {l₁ l₂ : List α} :
    (l₁ ++ l₂).mapM f = (return (← l₁.mapM f) ++ (← l₂.mapM f)) := by induction l₁ <;> simp [*]

/-! ### forM -/

-- We use `List.forM` as the simp normal form, rather that `ForM.forM`.
-- As such we need to replace `List.forM_nil` and `List.forM_cons` from Lean:

@[simp] theorem forM_nil' [Monad m] : ([] : List α).forM f = (pure .unit : m PUnit) := rfl

@[simp] theorem forM_cons' [Monad m] :
    (a::as).forM f = (f a >>= fun _ => as.forM f : m PUnit) :=
  List.forM_cons _ _ _

/-! ### eraseIdx -/

@[simp] theorem eraseIdx_nil : ([] : List α).eraseIdx i = [] := rfl
@[simp] theorem eraseIdx_cons_zero : (a::as).eraseIdx 0 = as := rfl
@[simp] theorem eraseIdx_cons_succ : (a::as).eraseIdx (i+1) = a :: as.eraseIdx i := rfl

/-! ### find? -/

@[simp] theorem find?_nil : ([] : List α).find? p = none := rfl
theorem find?_cons : (a::as).find? p = match p a with | true => some a | false => as.find? p :=
  rfl

/-! ### filter -/

@[simp] theorem filter_nil (p : α → Bool) : filter p [] = [] := rfl

@[simp] theorem filter_cons_of_pos {p : α → Bool} {a : α} (l) (pa : p a) :
    filter p (a :: l) = a :: filter p l := by rw [filter, pa]

@[simp] theorem filter_cons_of_neg {p : α → Bool} {a : α} (l) (pa : ¬ p a) :
    filter p (a :: l) = filter p l := by rw [filter, eq_false_of_ne_true pa]

theorem filter_cons :
    (x :: xs : List α).filter p = if p x then x :: (xs.filter p) else xs.filter p := by
  split <;> simp [*]

theorem mem_filter : x ∈ filter p as ↔ x ∈ as ∧ p x := by
  induction as with
  | nil => simp [filter]
  | cons a as ih =>
    by_cases h : p a
    · simp_all [or_and_left]
    · simp_all [or_and_right]

theorem filter_eq_nil {l} : filter p l = [] ↔ ∀ a, a ∈ l → ¬p a := by
  simp only [eq_nil_iff_forall_not_mem, mem_filter, not_and]

/-! ### findSome? -/

@[simp] theorem findSome?_nil : ([] : List α).findSome? f = none := rfl
theorem findSome?_cons {f : α → Option β} :
    (a::as).findSome? f = match f a with | some b => some b | none => as.findSome? f :=
  rfl

/-! ### replace -/

@[simp] theorem replace_nil [BEq α] : ([] : List α).replace a b = [] := rfl
theorem replace_cons [BEq α] {a : α} :
    (a::as).replace b c = match a == b with | true => c::as | false => a :: replace as b c :=
  rfl
@[simp] theorem replace_cons_self [BEq α] [LawfulBEq α] {a : α} : (a::as).replace a b = b::as := by
  simp [replace_cons]

/-! ### elem -/

@[simp] theorem elem_nil [BEq α] : ([] : List α).elem a = false := rfl
theorem elem_cons [BEq α] {a : α} :
    (a::as).elem b = match b == a with | true => true | false => as.elem b :=
  rfl
@[simp] theorem elem_cons_self [BEq α] [LawfulBEq α] {a : α} : (a::as).elem a = true := by
  simp [elem_cons]

/-! ### lookup -/

@[simp] theorem lookup_nil [BEq α] : ([] : List (α × β)).lookup a = none := rfl
theorem lookup_cons [BEq α] {k : α} :
    ((k,b)::es).lookup a = match a == k with | true => some b | false => es.lookup a :=
  rfl
@[simp] theorem lookup_cons_self [BEq α] [LawfulBEq α] {k : α} : ((k,b)::es).lookup k = some b := by
  simp [lookup_cons]

/-! ### zipWith -/

@[simp] theorem zipWith_nil_left {f : α → β → γ} : zipWith f [] l = [] := by
  rfl

@[simp] theorem zipWith_nil_right {f : α → β → γ} : zipWith f l [] = [] := by
  simp [zipWith]

@[simp] theorem zipWith_cons_cons {f : α → β → γ} :
    zipWith f (a :: as) (b :: bs) = f a b :: zipWith f as bs := by
  rfl

theorem zipWith_get? {f : α → β → γ} :
    (List.zipWith f as bs).get? i = match as.get? i, bs.get? i with
      | some a, some b => some (f a b) | _, _ => none := by
  induction as generalizing bs i with
  | nil => cases bs with
    | nil => simp
    | cons b bs => simp
  | cons a as aih => cases bs with
    | nil => simp
    | cons b bs => cases i <;> simp_all

/-! ### zipWithAll -/

theorem zipWithAll_get? {f : Option α → Option β → γ} :
    (zipWithAll f as bs).get? i = match as.get? i, bs.get? i with
      | none, none => .none | a?, b? => some (f a? b?) := by
  induction as generalizing bs i with
  | nil => induction bs generalizing i with
    | nil => simp
    | cons b bs bih => cases i <;> simp_all
  | cons a as aih => cases bs with
    | nil =>
      specialize @aih []
      cases i <;> simp_all
    | cons b bs => cases i <;> simp_all

/-! ### zip -/

@[simp] theorem zip_nil_left : zip ([] : List α) (l : List β)  = [] := by
  rfl

@[simp] theorem zip_nil_right : zip (l : List α) ([] : List β)  = [] := by
  simp [zip]

@[simp] theorem zip_cons_cons : zip (a :: as) (b :: bs) = (a, b) :: zip as bs := by
  rfl

/-! ### unzip -/

@[simp] theorem unzip_nil : ([] : List (α × β)).unzip = ([], []) := rfl
@[simp] theorem unzip_cons {h : α × β} :
    (h :: t).unzip = match unzip t with | (al, bl) => (h.1::al, h.2::bl) := rfl

/-! ### all / any -/

@[simp] theorem all_eq_true {l : List α} : l.all p ↔ ∀ x, x ∈ l →  p x := by induction l <;> simp [*]

@[simp] theorem any_eq_true {l : List α} : l.any p ↔ ∃ x, x ∈ l ∧ p x := by induction l <;> simp [*]

/-! ### enumFrom -/

@[simp] theorem enumFrom_nil : ([] : List α).enumFrom i = [] := rfl
@[simp] theorem enumFrom_cons : (a::as).enumFrom i = (i, a) :: as.enumFrom (i+1) := rfl

/-! ### iota -/

@[simp] theorem iota_zero : iota 0 = [] := rfl
@[simp] theorem iota_succ : iota (i+1) = (i+1) :: iota i := rfl

/-! ### intersperse -/

@[simp] theorem intersperse_nil (sep : α) : ([] : List α).intersperse sep = [] := rfl
@[simp] theorem intersperse_single (sep : α) : [x].intersperse sep = [x] := rfl
@[simp] theorem intersperse_cons₂ (sep : α) :
    (x::y::zs).intersperse sep = x::sep::((y::zs).intersperse sep) := rfl

/-! ### isPrefixOf -/

@[simp] theorem isPrefixOf_nil_left [BEq α] : isPrefixOf ([] : List α) l = true := by
  simp [isPrefixOf]
@[simp] theorem isPrefixOf_cons_nil [BEq α] : isPrefixOf (a::as) ([] : List α) = false := rfl
theorem isPrefixOf_cons₂ [BEq α] {a : α} :
    isPrefixOf (a::as) (b::bs) = (a == b && isPrefixOf as bs) := rfl
@[simp] theorem isPrefixOf_cons₂_self [BEq α] [LawfulBEq α] {a : α} :
    isPrefixOf (a::as) (a::bs) = isPrefixOf as bs := by simp [isPrefixOf_cons₂]

/-! ### isEqv -/

@[simp] theorem isEqv_nil_nil : isEqv ([] : List α) [] eqv = true := rfl
@[simp] theorem isEqv_nil_cons : isEqv ([] : List α) (a::as) eqv = false := rfl
@[simp] theorem isEqv_cons_nil : isEqv (a::as : List α) [] eqv = false := rfl
theorem isEqv_cons₂ : isEqv (a::as) (b::bs) eqv = (eqv a b && isEqv as bs eqv) := rfl

/-! ### dropLast -/

@[simp] theorem dropLast_nil : ([] : List α).dropLast = [] := rfl
@[simp] theorem dropLast_single : [x].dropLast = [] := rfl
@[simp] theorem dropLast_cons₂ :
    (x::y::zs).dropLast = x :: (y::zs).dropLast := rfl

-- We may want to replace these `simp` attributes with explicit equational lemmas,
-- as we already have for all the non-monadic functions.
attribute [simp] mapA forA filterAuxM firstM anyM allM findM? findSomeM?

-- Previously `range.loop`, `mapM.loop`, `filterMapM.loop`, `forIn.loop`, `forIn'.loop`
-- had attribute `@[simp]`.
-- We don't currently provide simp lemmas,
-- as this is an internal implementation and they don't seem to be needed.

/-! ### minimum? -/

@[simp] theorem minimum?_nil [Min α] : ([] : List α).minimum? = none := rfl

-- We don't put `@[simp]` on `minimum?_cons`,
-- because the definition in terms of `foldl` is not useful for proofs.
theorem minimum?_cons [Min α] {xs : List α} : (x :: xs).minimum? = foldl min x xs := rfl

@[simp] theorem minimum?_eq_none_iff {xs : List α} [Min α] : xs.minimum? = none ↔ xs = [] := by
  cases xs <;> simp [minimum?]

theorem minimum?_mem [Min α] (min_eq_or : ∀ a b : α, min a b = a ∨ min a b = b) :
    {xs : List α} → xs.minimum? = some a → a ∈ xs := by
  intro xs
  match xs with
  | nil => simp
  | x :: xs =>
    simp only [minimum?_cons, Option.some.injEq, List.mem_cons]
    intro eq
    induction xs generalizing x with
    | nil =>
      simp at eq
      simp [eq]
    | cons y xs ind =>
      simp at eq
      have p := ind _ eq
      cases p with
      | inl p =>
        cases min_eq_or x y with | _ q => simp [p, q]
      | inr p => simp [p, mem_cons]

theorem le_minimum?_iff [Min α] [LE α]
    (le_min_iff : ∀ a b c : α, a ≤ min b c ↔ a ≤ b ∧ a ≤ c) :
    {xs : List α} → xs.minimum? = some a → ∀ x, x ≤ a ↔ ∀ b, b ∈ xs → x ≤ b
  | nil => by simp
  | cons x xs => by
    rw [minimum?]
    intro eq y
    simp only [Option.some.injEq] at eq
    induction xs generalizing x with
    | nil =>
      simp at eq
      simp [eq]
    | cons z xs ih =>
      simp at eq
      simp [ih _ eq, le_min_iff, and_assoc]

-- This could be refactored by designing appropriate typeclasses to replace `le_refl`, `min_eq_or`,
-- and `le_min_iff`.
theorem minimum?_eq_some_iff [Min α] [LE α] [anti : Antisymm ((· : α) ≤ ·)]
    (le_refl : ∀ a : α, a ≤ a)
    (min_eq_or : ∀ a b : α, min a b = a ∨ min a b = b)
    (le_min_iff : ∀ a b c : α, a ≤ min b c ↔ a ≤ b ∧ a ≤ c) {xs : List α} :
    xs.minimum? = some a ↔ a ∈ xs ∧ ∀ b, b ∈ xs → a ≤ b := by
  refine ⟨fun h => ⟨minimum?_mem min_eq_or h, (le_minimum?_iff le_min_iff h _).1 (le_refl _)⟩, ?_⟩
  intro ⟨h₁, h₂⟩
  cases xs with
  | nil => simp at h₁
  | cons x xs =>
    exact congrArg some <| anti.1
      ((le_minimum?_iff le_min_iff (xs := x::xs) rfl _).1 (le_refl _) _ h₁)
      (h₂ _ (minimum?_mem min_eq_or (xs := x::xs) rfl))

@[simp] theorem get_cons_succ {as : List α} {h : i + 1 < (a :: as).length} :
  (a :: as).get ⟨i+1, h⟩ = as.get ⟨i, Nat.lt_of_succ_lt_succ h⟩ := rfl

@[simp] theorem get_cons_succ' {as : List α} {i : Fin as.length} :
  (a :: as).get i.succ = as.get i := rfl

@[simp] theorem set_nil (n : Nat) (a : α) : [].set n a = [] := rfl

@[simp] theorem set_zero (x : α) (xs : List α) (a : α) :
  (x :: xs).set 0 a = a :: xs := rfl

@[simp] theorem set_succ (x : α) (xs : List α) (n : Nat) (a : α) :
  (x :: xs).set n.succ a = x :: xs.set n a := rfl

@[simp] theorem get_set_eq (l : List α) (i : Nat) (a : α) (h : i < (l.set i a).length) :
    (l.set i a).get ⟨i, h⟩ = a :=
  match l, i with
  | [], _ => by
    simp at h
    contradiction
  | _ :: _, 0 => by
    simp
  | _ :: l, i + 1 => by
    simp [get_set_eq l]

@[simp] theorem get_set_ne (l : List α) {i j : Nat} (h : i ≠ j) (a : α)
    (hj : j < (l.set i a).length) :
    (l.set i a).get ⟨j, hj⟩ = l.get ⟨j, by simp at hj; exact hj⟩ :=
  match l, i, j with
  | [], _, _ => by
    simp
  | _ :: _, 0, 0 => by
    contradiction
  | _ :: _, 0, _ + 1 => by
    simp
  | _ :: _, _ + 1, 0 => by
    simp
  | _ :: l, i + 1, j + 1 => by
    have g : i ≠ j := h ∘ congrArg (· + 1)
    simp [get_set_ne l g]

end List

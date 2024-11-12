/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
prelude
import Init.Data.Option.BasicAux
import Init.Data.Option.Instances
import Init.Data.BEq
import Init.Classical
import Init.Ext

namespace Option

theorem mem_iff {a : α} {b : Option α} : a ∈ b ↔ b = some a := .rfl

theorem mem_some {a b : α} : a ∈ some b ↔ b = a := by simp

theorem mem_some_self (a : α) : a ∈ some a := mem_some.2 rfl

theorem some_ne_none (x : α) : some x ≠ none := nofun

protected theorem «forall» {p : Option α → Prop} : (∀ x, p x) ↔ p none ∧ ∀ x, p (some x) :=
  ⟨fun h => ⟨h _, fun _ => h _⟩, fun h x => Option.casesOn x h.1 h.2⟩

protected theorem «exists» {p : Option α → Prop} :
    (∃ x, p x) ↔ p none ∨ ∃ x, p (some x) :=
  ⟨fun | ⟨none, hx⟩ => .inl hx | ⟨some x, hx⟩ => .inr ⟨x, hx⟩,
   fun | .inl h => ⟨_, h⟩ | .inr ⟨_, hx⟩ => ⟨_, hx⟩⟩

theorem get_mem : ∀ {o : Option α} (h : isSome o), o.get h ∈ o
  | some _, _ => rfl

theorem get_of_mem : ∀ {o : Option α} (h : isSome o), a ∈ o → o.get h = a
  | _, _, rfl => rfl

theorem not_mem_none (a : α) : a ∉ (none : Option α) := nofun

theorem getD_of_ne_none {x : Option α} (hx : x ≠ none) (y : α) : some (x.getD y) = x := by
  cases x; {contradiction}; rw [getD_some]

theorem getD_eq_iff {o : Option α} {a b} : o.getD a = b ↔ (o = some b ∨ o = none ∧ a = b) := by
  cases o <;> simp

@[simp] theorem get!_none [Inhabited α] : (none : Option α).get! = default := rfl

@[simp] theorem get!_some [Inhabited α] {a : α} : (some a).get! = a := rfl

theorem get_eq_get! [Inhabited α] : (o : Option α) → {h : o.isSome} → o.get h = o.get!
  | some _, _ => rfl

theorem get_eq_getD {fallback : α} : (o : Option α) → {h : o.isSome} → o.get h = o.getD fallback
  | some _, _ => rfl

theorem some_get! [Inhabited α] : (o : Option α) → o.isSome → some (o.get!) = o
  | some _, _ => rfl

theorem get!_eq_getD_default [Inhabited α] (o : Option α) : o.get! = o.getD default := rfl

theorem mem_unique {o : Option α} {a b : α} (ha : a ∈ o) (hb : b ∈ o) : a = b :=
  some.inj <| ha ▸ hb

@[ext] theorem ext : ∀ {o₁ o₂ : Option α}, (∀ a, a ∈ o₁ ↔ a ∈ o₂) → o₁ = o₂
  | none, none, _ => rfl
  | some _, _, H => ((H _).1 rfl).symm
  | _, some _, H => (H _).2 rfl

theorem eq_none_iff_forall_not_mem : o = none ↔ ∀ a, a ∉ o :=
  ⟨fun e a h => by rw [e] at h; (cases h), fun h => ext <| by simp; exact h⟩

theorem isSome_iff_exists : isSome x ↔ ∃ a, x = some a := by cases x <;> simp [isSome]

theorem isSome_eq_isSome : (isSome x = isSome y) ↔ (x = none ↔ y = none) := by
  cases x <;> cases y <;> simp

@[simp] theorem not_isSome : isSome a = false ↔ a.isNone = true := by
  cases a <;> simp

theorem eq_some_iff_get_eq : o = some a ↔ ∃ h : o.isSome, o.get h = a := by
  cases o <;> simp

theorem eq_some_of_isSome : ∀ {o : Option α} (h : o.isSome), o = some (o.get h)
  | some _, _ => rfl

theorem isSome_iff_ne_none : o.isSome ↔ o ≠ none := by
  cases o <;> simp

theorem not_isSome_iff_eq_none : ¬o.isSome ↔ o = none := by
  cases o <;> simp

theorem ne_none_iff_isSome : o ≠ none ↔ o.isSome := by cases o <;> simp

theorem ne_none_iff_exists : o ≠ none ↔ ∃ x, some x = o := by cases o <;> simp

theorem ne_none_iff_exists' : o ≠ none ↔ ∃ x, o = some x :=
  ne_none_iff_exists.trans <| exists_congr fun _ => eq_comm

theorem bex_ne_none {p : Option α → Prop} : (∃ x, ∃ (_ : x ≠ none), p x) ↔ ∃ x, p (some x) :=
  ⟨fun ⟨x, hx, hp⟩ => ⟨x.get <| ne_none_iff_isSome.1 hx, by rwa [some_get]⟩,
    fun ⟨x, hx⟩ => ⟨some x, some_ne_none x, hx⟩⟩

theorem ball_ne_none {p : Option α → Prop} : (∀ x (_ : x ≠ none), p x) ↔ ∀ x, p (some x) :=
  ⟨fun h x => h (some x) (some_ne_none x),
    fun h x hx => by
      have := h <| x.get <| ne_none_iff_isSome.1 hx
      simp [some_get] at this ⊢
      exact this⟩

@[simp] theorem pure_def : pure = @some α := rfl

@[simp] theorem bind_eq_bind : bind = @Option.bind α β := rfl

@[simp] theorem bind_some (x : Option α) : x.bind some = x := by cases x <;> rfl

@[simp] theorem bind_none (x : Option α) : x.bind (fun _ => none (α := β)) = none := by
  cases x <;> rfl

theorem bind_eq_some : x.bind f = some b ↔ ∃ a, x = some a ∧ f a = some b := by
  cases x <;> simp

@[simp] theorem bind_eq_none {o : Option α} {f : α → Option β} :
    o.bind f = none ↔ ∀ a, o = some a → f a = none := by cases o <;> simp

theorem bind_eq_none' {o : Option α} {f : α → Option β} :
    o.bind f = none ↔ ∀ b a, a ∈ o → b ∉ f a := by
  simp only [eq_none_iff_forall_not_mem, not_exists, not_and, mem_def, bind_eq_some]

theorem mem_bind_iff {o : Option α} {f : α → Option β} :
    b ∈ o.bind f ↔ ∃ a, a ∈ o ∧ b ∈ f a := by
  cases o <;> simp

theorem bind_comm {f : α → β → Option γ} (a : Option α) (b : Option β) :
    (a.bind fun x => b.bind (f x)) = b.bind fun y => a.bind fun x => f x y := by
  cases a <;> cases b <;> rfl

theorem bind_assoc (x : Option α) (f : α → Option β) (g : β → Option γ) :
    (x.bind f).bind g = x.bind fun y => (f y).bind g := by cases x <;> rfl

theorem join_eq_some : x.join = some a ↔ x = some (some a) := by
  simp [bind_eq_some]

theorem join_ne_none : x.join ≠ none ↔ ∃ z, x = some (some z) := by
  simp only [ne_none_iff_exists', join_eq_some, iff_self]

theorem join_ne_none' : ¬x.join = none ↔ ∃ z, x = some (some z) :=
  join_ne_none

theorem join_eq_none : o.join = none ↔ o = none ∨ o = some none :=
  match o with | none | some none | some (some _) => by simp

theorem bind_id_eq_join {x : Option (Option α)} : x.bind id = x.join := rfl

@[simp] theorem map_eq_map : Functor.map f = Option.map f := rfl

theorem map_none : f <$> none = none := rfl

theorem map_some : f <$> some a = some (f a) := rfl

@[simp] theorem map_eq_some' : x.map f = some b ↔ ∃ a, x = some a ∧ f a = b := by cases x <;> simp

theorem map_eq_some : f <$> x = some b ↔ ∃ a, x = some a ∧ f a = b := map_eq_some'

@[simp] theorem map_eq_none' : x.map f = none ↔ x = none := by
  cases x <;> simp [map_none', map_some', eq_self_iff_true]

theorem isSome_map {x : Option α} : (f <$> x).isSome = x.isSome := by
  cases x <;> simp

@[simp] theorem isSome_map' {x : Option α} : (x.map f).isSome = x.isSome := by
  cases x <;> simp

@[simp] theorem isNone_map' {x : Option α} : (x.map f).isNone = x.isNone := by
  cases x <;> simp

theorem map_eq_none : f <$> x = none ↔ x = none := map_eq_none'

theorem map_eq_bind {x : Option α} : x.map f = x.bind (some ∘ f) := by
  cases x <;> simp [Option.bind]

theorem map_congr {x : Option α} (h : ∀ a, a ∈ x → f a = g a) : x.map f = x.map g := by
  cases x <;> simp only [map_none', map_some', h, mem_def]

@[simp] theorem map_id_fun {α : Type u} : Option.map (id : α → α) = id := by
  funext; simp [map_id]

theorem map_id' {x : Option α} : (x.map fun a => a) = x := congrFun map_id x

@[simp] theorem map_id_fun' {α : Type u} : Option.map (fun (a : α) => a) = id := by
  funext; simp [map_id']

theorem get_map {f : α → β} {o : Option α} {h : (o.map f).isSome} :
    (o.map f).get h = f (o.get (by simpa using h)) := by
  cases o with
  | none => simp at h
  | some a => simp

@[simp] theorem map_map (h : β → γ) (g : α → β) (x : Option α) :
    (x.map g).map h = x.map (h ∘ g) := by
  cases x <;> simp only [map_none', map_some', ·∘·]

theorem comp_map (h : β → γ) (g : α → β) (x : Option α) : x.map (h ∘ g) = (x.map g).map h :=
  (map_map ..).symm

@[simp] theorem map_comp_map (f : α → β) (g : β → γ) :
    Option.map g ∘ Option.map f = Option.map (g ∘ f) := by funext x; simp

theorem mem_map_of_mem (g : α → β) (h : a ∈ x) : g a ∈ Option.map g x := h.symm ▸ map_some' ..

@[simp] theorem map_if {f : α → β} [Decidable c] :
     (if c then some a else none).map f = if c then some (f a) else none := by
  split <;> rfl

@[simp] theorem map_dif {f : α → β} [Decidable c] {a : c → α} :
     (if h : c then some (a h) else none).map f = if h : c then some (f (a h)) else none := by
  split <;> rfl

@[simp] theorem filter_none (p : α → Bool) : none.filter p = none := rfl

theorem filter_some : Option.filter p (some a) = if p a then some a else none := rfl

theorem isSome_filter_of_isSome (p : α → Bool) (o : Option α) (h : (o.filter p).isSome) :
    o.isSome := by
  cases o <;> simp at h ⊢

@[simp] theorem filter_eq_none {p : α → Bool} :
    o.filter p = none ↔ o = none ∨ ∀ a, a ∈ o → ¬ p a := by
  cases o <;> simp [filter_some]

@[simp] theorem filter_eq_some {o : Option α} {p : α → Bool} :
    o.filter p = some a ↔ a ∈ o ∧ p a := by
  cases o with
  | none => simp
  | some a =>
    simp [filter_some]
    split <;> rename_i h
    · simp only [some.injEq, iff_self_and]
      rintro rfl
      exact h
    · simp only [reduceCtorEq, false_iff, not_and, Bool.not_eq_true]
      rintro rfl
      simpa using h

theorem mem_filter_iff {p : α → Bool} {a : α} {o : Option α} :
    a ∈ o.filter p ↔ a ∈ o ∧ p a := by
  simp

@[simp] theorem all_guard (p : α → Prop) [DecidablePred p] (a : α) :
    Option.all q (guard p a) = (!p a || q a) := by
  simp only [guard]
  split <;> simp_all

@[simp] theorem any_guard (p : α → Prop) [DecidablePred p] (a : α) :
    Option.any q (guard p a) = (p a && q a) := by
  simp only [guard]
  split <;> simp_all

theorem bind_map_comm {α β} {x : Option (Option α)} {f : α → β} :
    x.bind (Option.map f) = (x.map (Option.map f)).bind id := by cases x <;> simp

theorem bind_map {f : α → β} {g : β → Option γ} {x : Option α} :
    (x.map f).bind g = x.bind (g ∘ f) := by cases x <;> simp

@[simp] theorem map_bind {f : α → Option β} {g : β → γ} {x : Option α} :
    (x.bind f).map g = x.bind (Option.map g ∘ f) := by cases x <;> simp

theorem join_map_eq_map_join {f : α → β} {x : Option (Option α)} :
    (x.map (Option.map f)).join = x.join.map f := by cases x <;> simp

theorem join_join {x : Option (Option (Option α))} : x.join.join = (x.map join).join := by
  cases x <;> simp

theorem mem_of_mem_join {a : α} {x : Option (Option α)} (h : a ∈ x.join) : some a ∈ x :=
  h.symm ▸ join_eq_some.1 h

@[simp] theorem some_orElse (a : α) (x : Option α) : (some a <|> x) = some a := rfl

@[simp] theorem none_orElse (x : Option α) : (none <|> x) = x := rfl

@[simp] theorem orElse_none (x : Option α) : (x <|> none) = x := by cases x <;> rfl

theorem map_orElse {x y : Option α} : (x <|> y).map f = (x.map f <|> y.map f) := by
  cases x <;> simp

@[simp] theorem guard_eq_some [DecidablePred p] : guard p a = some b ↔ a = b ∧ p a :=
  if h : p a then by simp [Option.guard, h] else by simp [Option.guard, h]

@[simp] theorem guard_isSome [DecidablePred p] : (Option.guard p a).isSome ↔ p a :=
  if h : p a then by simp [Option.guard, h] else by simp [Option.guard, h]

@[simp] theorem guard_eq_none [DecidablePred p] : Option.guard p a = none ↔ ¬ p a :=
  if h : p a then by simp [Option.guard, h] else by simp [Option.guard, h]

@[simp] theorem guard_pos [DecidablePred p] (h : p a) : Option.guard p a = some a := by
  simp [Option.guard, h]

@[congr] theorem guard_congr {f g : α → Prop} [DecidablePred f] [DecidablePred g]
    (h : ∀ a, f a ↔ g a):
    guard f = guard g := by
  funext a
  simp [guard, h]

@[simp] theorem guard_false {α} :
    guard (fun (_ : α) => False) = fun _ => none := by
  funext a
  simp [guard]

@[simp] theorem guard_true {α} :
    guard (fun (_ : α) => True) = some := by
  funext a
  simp [guard]

theorem guard_comp {p : α → Prop} [DecidablePred p] {f : β → α} :
    guard p ∘ f = Option.map f ∘ guard (p ∘ f) := by
  ext1 b
  simp [guard]

theorem liftOrGet_eq_or_eq {f : α → α → α} (h : ∀ a b, f a b = a ∨ f a b = b) :
    ∀ o₁ o₂, liftOrGet f o₁ o₂ = o₁ ∨ liftOrGet f o₁ o₂ = o₂
  | none, none => .inl rfl
  | some _, none => .inl rfl
  | none, some _ => .inr rfl
  | some a, some b => by have := h a b; simp [liftOrGet] at this ⊢; exact this

@[simp] theorem liftOrGet_none_left {f} {b : Option α} : liftOrGet f none b = b := by
  cases b <;> rfl

@[simp] theorem liftOrGet_none_right {f} {a : Option α} : liftOrGet f a none = a := by
  cases a <;> rfl

@[simp] theorem liftOrGet_some_some {f} {a b : α} :
  liftOrGet f (some a) (some b) = f a b := rfl

@[simp] theorem elim_none (x : β) (f : α → β) : none.elim x f = x := rfl

@[simp] theorem elim_some (x : β) (f : α → β) (a : α) : (some a).elim x f = f a := rfl

@[simp] theorem getD_map (f : α → β) (x : α) (o : Option α) :
  (o.map f).getD (f x) = f (getD o x) := by cases o <;> rfl

section choice

attribute [local instance] Classical.propDecidable

/-- An arbitrary `some a` with `a : α` if `α` is nonempty, and otherwise `none`. -/
noncomputable def choice (α : Type _) : Option α :=
  if h : Nonempty α then some (Classical.choice h) else none

theorem choice_eq {α : Type _} [Subsingleton α] (a : α) : choice α = some a := by
  simp [choice]
  rw [dif_pos (⟨a⟩ : Nonempty α)]
  simp; apply Subsingleton.elim

theorem choice_isSome_iff_nonempty {α : Type _} : (choice α).isSome ↔ Nonempty α :=
  ⟨fun h => ⟨(choice α).get h⟩, fun h => by simp only [choice, dif_pos h, isSome_some]⟩

end choice

@[simp] theorem toList_some (a : α) : (a : Option α).toList = [a] := rfl

@[simp] theorem toList_none (α : Type _) : (none : Option α).toList = [] := rfl

-- See `Init.Data.Option.List` for lemmas about `toList`.

@[simp] theorem some_or : (some a).or o = some a := rfl
@[simp] theorem none_or : none.or o = o := rfl

@[deprecated some_or (since := "2024-11-03")] theorem or_some : (some a).or o = some a := rfl

/-- This will be renamed to `or_some` once the existing deprecated lemma is removed. -/
@[simp] theorem or_some' {o : Option α} : o.or (some a) = o.getD a := by
  cases o <;> rfl

theorem or_eq_bif : or o o' = bif o.isSome then o else o' := by
  cases o <;> rfl

@[simp] theorem isSome_or : (or o o').isSome = (o.isSome || o'.isSome) := by
  cases o <;> rfl

@[simp] theorem isNone_or : (or o o').isNone = (o.isNone && o'.isNone) := by
  cases o <;> rfl

@[simp] theorem or_eq_none : or o o' = none ↔ o = none ∧ o' = none := by
  cases o <;> simp

@[simp] theorem or_eq_some : or o o' = some a ↔ o = some a ∨ (o = none ∧ o' = some a) := by
  cases o <;> simp

theorem or_assoc : or (or o₁ o₂) o₃ = or o₁ (or o₂ o₃) := by
  cases o₁ <;> cases o₂ <;> rfl
instance : Std.Associative (or (α := α)) := ⟨@or_assoc _⟩

@[simp]
theorem or_none : or o none = o := by
  cases o <;> rfl
instance : Std.LawfulIdentity (or (α := α)) none where
  left_id := @none_or _
  right_id := @or_none _

@[simp]
theorem or_self : or o o = o := by
  cases o <;> rfl
instance : Std.IdempotentOp (or (α := α)) := ⟨@or_self _⟩

theorem or_eq_orElse : or o o' = o.orElse (fun _ => o') := by
  cases o <;> rfl

theorem map_or : f <$> or o o' = (f <$> o).or (f <$> o') := by
  cases o <;> rfl

theorem map_or' : (or o o').map f = (o.map f).or (o'.map f) := by
  cases o <;> rfl

theorem or_of_isSome {o o' : Option α} (h : o.isSome) : o.or o' = o := by
  match o, h with
  | some _, _ => simp

theorem or_of_isNone {o o' : Option α} (h : o.isNone) : o.or o' = o' := by
  match o, h with
  | none, _ => simp

/-! ### beq -/

section beq

variable [BEq α]

@[simp] theorem none_beq_none : ((none : Option α) == none) = true := rfl
@[simp] theorem none_beq_some (a : α) : ((none : Option α) == some a) = false := rfl
@[simp] theorem some_beq_none (a : α) : ((some a : Option α) == none) = false := rfl
@[simp] theorem some_beq_some {a b : α} : (some a == some b) = (a == b) := rfl

@[simp] theorem reflBEq_iff : ReflBEq (Option α) ↔ ReflBEq α := by
  constructor
  · intro h
    constructor
    intro a
    suffices (some a == some a) = true by
      simpa only [some_beq_some]
    simp
  · intro h
    constructor
    · rintro (_ | a) <;> simp

@[simp] theorem lawfulBEq_iff : LawfulBEq (Option α) ↔ LawfulBEq α := by
  constructor
  · intro h
    constructor
    · intro a b h
      apply Option.some.inj
      apply eq_of_beq
      simpa
    · intro a
      suffices (some a == some a) = true by
        simpa only [some_beq_some]
      simp
  · intro h
    constructor
    · intro a b h
      simpa using h
    · intro a
      simp

end beq

/-! ### ite -/
section ite

@[simp] theorem dite_none_left_eq_some {p : Prop} [Decidable p] {b : ¬p → Option β} :
    (if h : p then none else b h) = some a ↔ ∃ h, b h = some a := by
  split <;> simp_all

@[simp] theorem dite_none_right_eq_some {p : Prop} [Decidable p] {b : p → Option α} :
    (if h : p then b h else none) = some a ↔ ∃ h, b h = some a := by
  split <;> simp_all

@[simp] theorem some_eq_dite_none_left {p : Prop} [Decidable p] {b : ¬p → Option β} :
    some a = (if h : p then none else b h) ↔ ∃ h, some a = b h := by
  split <;> simp_all

@[simp] theorem some_eq_dite_none_right {p : Prop} [Decidable p] {b : p → Option α} :
    some a = (if h : p then b h else none) ↔ ∃ h, some a = b h := by
  split <;> simp_all

@[simp] theorem ite_none_left_eq_some {p : Prop} [Decidable p] {b : Option β} :
    (if p then none else b) = some a ↔ ¬ p ∧ b = some a := by
  split <;> simp_all

@[simp] theorem ite_none_right_eq_some {p : Prop} [Decidable p] {b : Option α} :
    (if p then b else none) = some a ↔ p ∧ b = some a := by
  split <;> simp_all

@[simp] theorem some_eq_ite_none_left {p : Prop} [Decidable p] {b : Option β} :
    some a = (if p then none else b) ↔ ¬ p ∧ some a = b := by
  split <;> simp_all

@[simp] theorem some_eq_ite_none_right {p : Prop} [Decidable p] {b : Option α} :
    some a = (if p then b else none) ↔ p ∧ some a = b := by
  split <;> simp_all

theorem mem_dite_none_left {x : α} [Decidable p] {l : ¬ p → Option α} :
    (x ∈ if h : p then none else l h) ↔ ∃ h : ¬ p, x ∈ l h := by
  simp

theorem mem_dite_none_right {x : α} [Decidable p] {l : p → Option α} :
    (x ∈ if h : p then l h else none) ↔ ∃ h : p, x ∈ l h := by
  simp

theorem mem_ite_none_left {x : α} [Decidable p] {l : Option α} :
    (x ∈ if p then none else l) ↔ ¬ p ∧ x ∈ l := by
  simp

theorem mem_ite_none_right {x : α} [Decidable p] {l : Option α} :
    (x ∈ if p then l else none) ↔ p ∧ x ∈ l := by
  simp

@[simp] theorem isSome_dite {p : Prop} [Decidable p] {b : p → β} :
    (if h : p then some (b h) else none).isSome = true ↔ p := by
  split <;> simpa
@[simp] theorem isSome_ite {p : Prop} [Decidable p] :
    (if p then some b else none).isSome = true ↔ p := by
  split <;> simpa
@[simp] theorem isSome_dite' {p : Prop} [Decidable p] {b : ¬ p → β} :
    (if h : p then none else some (b h)).isSome = true ↔ ¬ p := by
  split <;> simpa
@[simp] theorem isSome_ite' {p : Prop} [Decidable p] :
    (if p then none else some b).isSome = true ↔ ¬ p := by
  split <;> simpa

@[simp] theorem get_dite {p : Prop} [Decidable p] (b : p → β) (w) :
    (if h : p then some (b h) else none).get w = b (by simpa using w) := by
  split
  · simp
  · exfalso
    simp at w
    contradiction
@[simp] theorem get_ite {p : Prop} [Decidable p] (h) :
    (if p then some b else none).get h = b := by
  simpa using get_dite (p := p) (fun _ => b) (by simpa using h)
@[simp] theorem get_dite' {p : Prop} [Decidable p] (b : ¬ p → β) (w) :
    (if h : p then none else some (b h)).get w = b (by simpa using w) := by
  split
  · exfalso
    simp at w
    contradiction
  · simp
@[simp] theorem get_ite' {p : Prop} [Decidable p] (h) :
    (if p then none else some b).get h = b := by
  simpa using get_dite' (p := p) (fun _ => b) (by simpa using h)

end ite

/-! ### pbind -/

@[simp] theorem pbind_none : pbind none f = none := rfl
@[simp] theorem pbind_some : pbind (some a) f = f a (mem_some_self a) := rfl

@[simp] theorem map_pbind {o : Option α} {f : (a : α) → a ∈ o → Option β} {g : β → γ} :
    (o.pbind f).map g = o.pbind (fun a h => (f a h).map g) := by
  cases o <;> simp

@[congr] theorem pbind_congr {o o' : Option α} (ho : o = o')
    {f : (a : α) → a ∈ o → Option β} {g : (a : α) → a ∈ o' → Option β}
    (hf : ∀ a h, f a (ho ▸ h) = g a h) : o.pbind f = o'.pbind g := by
  subst ho
  exact (funext fun a => funext fun h => hf a h) ▸ Eq.refl (o.pbind f)

theorem pbind_eq_none_iff {o : Option α} {f : (a : α) → a ∈ o → Option β} :
    o.pbind f = none ↔ o = none ∨ ∃ a h, f a h = none := by
  cases o with
  | none => simp
  | some a =>
    simp only [pbind_some, reduceCtorEq, mem_def, some.injEq, false_or]
    constructor
    · intro h
      exact ⟨a, rfl, h⟩
    · rintro ⟨a, rfl, h⟩
      exact h

theorem pbind_isSome {o : Option α} {f : (a : α) → a ∈ o → Option β} :
    (o.pbind f).isSome = ∃ a h, (f a h).isSome := by
  cases o with
  | none => simp
  | some a =>
    simp only [pbind_some, mem_def, some.injEq, eq_iff_iff]
    constructor
    · intro h
      exact ⟨a, rfl, h⟩
    · rintro ⟨a, rfl, h⟩
      exact h

theorem pbind_eq_some_iff {o : Option α} {f : (a : α) → a ∈ o → Option β} {b : β} :
    o.pbind f = some b ↔ ∃ a h, f a h = some b := by
  cases o with
  | none => simp
  | some a =>
    simp only [pbind_some, mem_def, some.injEq]
    constructor
    · intro h
      exact ⟨a, rfl, h⟩
    · rintro ⟨a, rfl, h⟩
      exact h

/-! ### pmap -/

@[simp] theorem pmap_none {p : α → Prop} {f : ∀ (a : α), p a → β} {h} :
    pmap f none h = none := rfl

@[simp] theorem pmap_some {p : α → Prop} {f : ∀ (a : α), p a → β} {h}:
    pmap f (some a) h = f a (h a (mem_some_self a)) := rfl

@[simp] theorem pmap_eq_none_iff {p : α → Prop} {f : ∀ (a : α), p a → β} {h} :
    pmap f o h = none ↔ o = none := by
  cases o <;> simp

@[simp] theorem pmap_isSome {p : α → Prop} {f : ∀ (a : α), p a → β} {o : Option α} {h} :
    (pmap f o h).isSome = o.isSome := by
  cases o <;> simp

@[simp] theorem pmap_eq_some_iff {p : α → Prop} {f : ∀ (a : α), p a → β} {o : Option α} {h} :
    pmap f o h = some b ↔ ∃ (a : α) (h : p a), o = some a ∧ b = f a h := by
  cases o with
  | none => simp
  | some a =>
    simp only [pmap, eq_comm, some.injEq, exists_and_left, exists_eq_left']
    constructor
    · exact fun w => ⟨h a rfl, w⟩
    · rintro ⟨h, rfl⟩
      rfl

end Option

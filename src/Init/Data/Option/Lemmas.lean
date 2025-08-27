/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

prelude
public import Init.Data.Option.BasicAux
import all Init.Data.Option.BasicAux
public import Init.Data.Option.Instances
import all Init.Data.Option.Instances
public import Init.Data.BEq
public import Init.Classical
public import Init.Ext
public import Init.Grind.Tactics

public section

namespace Option

@[grind =] theorem default_eq_none : (default : Option α) = none := rfl

@[deprecated mem_def (since := "2025-04-07")]
theorem mem_iff {a : α} {b : Option α} : a ∈ b ↔ b = some a := .rfl

@[grind] theorem mem_some {a b : α} : a ∈ some b ↔ b = a := by simp

theorem mem_some_iff {a b : α} : a ∈ some b ↔ b = a := mem_some

theorem mem_some_self (a : α) : a ∈ some a := rfl

theorem some_ne_none (x : α) : some x ≠ none := nofun

protected theorem «forall» {p : Option α → Prop} : (∀ x, p x) ↔ p none ∧ ∀ x, p (some x) :=
  ⟨fun h => ⟨h _, fun _ => h _⟩, fun h x => Option.casesOn x h.1 h.2⟩

protected theorem «exists» {p : Option α → Prop} :
    (∃ x, p x) ↔ p none ∨ ∃ x, p (some x) :=
  ⟨fun | ⟨none, hx⟩ => .inl hx | ⟨some x, hx⟩ => .inr ⟨x, hx⟩,
   fun | .inl h => ⟨_, h⟩ | .inr ⟨_, hx⟩ => ⟨_, hx⟩⟩

theorem eq_none_or_eq_some (a : Option α) : a = none ∨ ∃ x, a = some x :=
  Option.exists.mp exists_eq'

theorem get_mem : ∀ {o : Option α} (h : isSome o), o.get h ∈ o
  | some _, _ => rfl

theorem get_of_mem : ∀ {o : Option α} (h : isSome o), a ∈ o → o.get h = a
  | _, _, rfl => rfl

theorem get_of_eq_some : ∀ {o : Option α} (h : isSome o), o = some a → o.get h = a
  | _, _, rfl => rfl

@[simp, grind] theorem not_mem_none (a : α) : a ∉ (none : Option α) := nofun

theorem getD_of_ne_none {x : Option α} (hx : x ≠ none) (y : α) : some (x.getD y) = x := by
  cases x; {contradiction}; rw [getD_some]

theorem getD_eq_iff {o : Option α} {a b} : o.getD a = b ↔ (o = some b ∨ o = none ∧ a = b) := by
  cases o <;> simp

@[simp, grind =] theorem get!_none [Inhabited α] : (none : Option α).get! = default := rfl

@[simp, grind =] theorem get!_some [Inhabited α] {a : α} : (some a).get! = a := rfl

theorem get_eq_get! [Inhabited α] : (o : Option α) → {h : o.isSome} → o.get h = o.get!
  | some _, _ => rfl

theorem get_eq_getD {fallback : α} : (o : Option α) → {h : o.isSome} → o.get h = o.getD fallback
  | some _, _ => rfl

theorem some_get! [Inhabited α] : (o : Option α) → o.isSome → some (o.get!) = o
  | some _, _ => rfl

theorem get!_eq_getD [Inhabited α] (o : Option α) : o.get! = o.getD default := rfl

theorem get_congr {o o' : Option α} {ho : o.isSome} (h : o = o') :
    o.get ho = o'.get (h ▸ ho) := by
  cases h; rfl

theorem get_inj {o1 o2 : Option α} {h1} {h2} :
    o1.get h1 = o2.get h2 ↔ o1 = o2 := by
  match o1, o2, h1, h2 with
  | some a, some b, _, _ => simp only [Option.get_some, Option.some.injEq]

theorem mem_unique {o : Option α} {a b : α} (ha : a ∈ o) (hb : b ∈ o) : a = b :=
  some.inj <| ha ▸ hb

theorem eq_some_unique {o : Option α} {a b : α} (ha : o = some a) (hb : o = some b) : a = b :=
  some.inj <| ha ▸ hb

-- This is not a good `@[grind ext]` lemma, as it results in too much case splitting.
@[ext] theorem ext : ∀ {o₁ o₂ : Option α}, (∀ a, o₁ = some a ↔ o₂ = some a) → o₁ = o₂
  | none, none, _ => rfl
  | some _, _, H => ((H _).1 rfl).symm
  | _, some _, H => (H _).2 rfl

theorem eq_none_iff_forall_ne_some : o = none ↔ ∀ a, o ≠ some a := by
  cases o <;> simp

theorem eq_none_iff_forall_some_ne : o = none ↔ ∀ a, some a ≠ o := by
  cases o <;> simp

theorem eq_none_iff_forall_not_mem : o = none ↔ ∀ a, a ∉ o :=
  eq_none_iff_forall_ne_some

theorem isSome_iff_exists : isSome x ↔ ∃ a, x = some a := by cases x <;> simp [isSome]

theorem isSome_eq_isSome : (isSome x = isSome y) ↔ (x = none ↔ y = none) := by
  cases x <;> cases y <;> simp

theorem isSome_of_mem {x : Option α} {y : α} (h : y ∈ x) : x.isSome := by
  cases x <;> trivial

theorem isSome_of_eq_some {x : Option α} {y : α} (h : x = some y) : x.isSome := by
  cases x <;> trivial

@[simp] theorem isSome_eq_false_iff : isSome a = false ↔ a.isNone = true := by
  cases a <;> simp

@[simp] theorem isNone_eq_false_iff : isNone a = false ↔ a.isSome = true := by
  cases a <;> simp

@[simp, grind =]
theorem not_isSome (a : Option α) : (!a.isSome) = a.isNone := by
  cases a <;> simp

@[simp]
theorem not_comp_isSome : (! ·) ∘ @Option.isSome α = Option.isNone := by
  funext
  simp

@[simp, grind =]
theorem not_isNone (a : Option α) : (!a.isNone) = a.isSome := by
  cases a <;> simp

@[simp]
theorem not_comp_isNone : (!·) ∘ @Option.isNone α = Option.isSome := by
  funext x
  simp

theorem eq_some_iff_get_eq : o = some a ↔ ∃ h : o.isSome, o.get h = a := by
  cases o <;> simp

theorem eq_some_of_isSome : ∀ {o : Option α} (h : o.isSome), o = some (o.get h)
  | some _, _ => rfl

theorem isSome_iff_ne_none : o.isSome ↔ o ≠ none := by
  cases o <;> simp

theorem not_isSome_iff_eq_none : ¬o.isSome ↔ o = none := by
  cases o <;> simp

theorem ne_none_iff_isSome : o ≠ none ↔ o.isSome := by cases o <;> simp

@[simp]
theorem any_true {o : Option α} : o.any (fun _ => true) = o.isSome := by
  cases o <;> simp

@[simp]
theorem any_false {o : Option α} : o.any (fun _ => false) = false := by
  cases o <;> simp

@[simp]
theorem all_true {o : Option α} : o.all (fun _ => true) = true := by
  cases o <;> simp

@[simp]
theorem all_false {o : Option α} : o.all (fun _ => false) = o.isNone := by
  cases o <;> simp

theorem ne_none_iff_exists : o ≠ none ↔ ∃ x, some x = o := by cases o <;> simp

theorem ne_none_iff_exists' : o ≠ none ↔ ∃ x, o = some x :=
  ne_none_iff_exists.trans <| exists_congr fun _ => eq_comm

theorem exists_ne_none {p : Option α → Prop} : (∃ x, x ≠ none ∧ p x) ↔ ∃ x, p (some x) :=
  ⟨fun ⟨x, hx, hp⟩ => ⟨x.get <| ne_none_iff_isSome.1 hx, by rwa [some_get]⟩,
    fun ⟨x, hx⟩ => ⟨some x, some_ne_none x, hx⟩⟩

@[deprecated exists_ne_none (since := "2025-04-04")]
theorem bex_ne_none {p : Option α → Prop} : (∃ x, ∃ (_ : x ≠ none), p x) ↔ ∃ x, p (some x) := by
  simp only [exists_prop, exists_ne_none]

theorem forall_ne_none {p : Option α → Prop} : (∀ x (_ : x ≠ none), p x) ↔ ∀ x, p (some x) :=
  ⟨fun h x => h (some x) (some_ne_none x),
    fun h x hx => by
      have := h <| x.get <| ne_none_iff_isSome.1 hx
      simp [some_get] at this ⊢
      exact this⟩

@[deprecated forall_ne_none (since := "2025-04-04")]
abbrev ball_ne_none := @forall_ne_none

@[simp] theorem pure_def : pure = @some α := rfl

@[grind =] theorem pure_apply : pure x = some x := rfl

@[simp] theorem bind_eq_bind : bind = @Option.bind α β := rfl

@[grind =] theorem bind_apply : bind x f = Option.bind x f := rfl

@[simp, grind =] theorem bind_fun_some (x : Option α) : x.bind some = x := by cases x <;> rfl

@[simp] theorem bind_fun_none (x : Option α) : x.bind (fun _ => none (α := β)) = none := by
  cases x <;> rfl

theorem bind_eq_some_iff : x.bind f = some b ↔ ∃ a, x = some a ∧ f a = some b := by
  cases x <;> simp

@[deprecated bind_eq_some_iff (since := "2025-04-10")]
abbrev bind_eq_some := @bind_eq_some_iff

@[simp] theorem bind_eq_none_iff {o : Option α} {f : α → Option β} :
    o.bind f = none ↔ ∀ a, o = some a → f a = none := by cases o <;> simp

@[deprecated bind_eq_none_iff (since := "2025-04-10")]
abbrev bind_eq_none := @bind_eq_none_iff

theorem bind_eq_none' {o : Option α} {f : α → Option β} :
    o.bind f = none ↔ ∀ b a, o = some a → f a ≠ some b := by
  cases o <;> simp [eq_none_iff_forall_ne_some]

@[grind =] theorem mem_bind_iff {o : Option α} {f : α → Option β} :
    b ∈ o.bind f ↔ ∃ a, a ∈ o ∧ b ∈ f a := by
  cases o <;> simp

theorem bind_comm {f : α → β → Option γ} (a : Option α) (b : Option β) :
    (a.bind fun x => b.bind (f x)) = b.bind fun y => a.bind fun x => f x y := by
  cases a <;> cases b <;> rfl

@[grind =]
theorem bind_assoc (x : Option α) (f : α → Option β) (g : β → Option γ) :
    (x.bind f).bind g = x.bind fun y => (f y).bind g := by cases x <;> rfl

theorem bind_congr {α β} {o : Option α} {f g : α → Option β} :
    (h : ∀ a, o = some a → f a = g a) → o.bind f = o.bind g := by
  cases o <;> simp

@[grind =]
theorem isSome_bind {α β : Type _} (x : Option α) (f : α → Option β) :
    (x.bind f).isSome = x.any (fun x => (f x).isSome) := by
  cases x <;> rfl

@[grind =]
theorem isNone_bind {α β : Type _} (x : Option α) (f : α → Option β) :
    (x.bind f).isNone = x.all (fun x => (f x).isNone) := by
  cases x <;> rfl

theorem isSome_of_isSome_bind {α β : Type _} {x : Option α} {f : α → Option β}
    (h : (x.bind f).isSome) : x.isSome := by
  cases x <;> trivial

theorem isSome_apply_of_isSome_bind {α β : Type _} {x : Option α} {f : α → Option β}
    (h : (x.bind f).isSome) : (f (x.get (isSome_of_isSome_bind h))).isSome := by
  cases x <;> trivial

@[simp, grind =] theorem get_bind {α β : Type _} {x : Option α} {f : α → Option β} (h : (x.bind f).isSome) :
    (x.bind f).get h = (f (x.get (isSome_of_isSome_bind h))).get
      (isSome_apply_of_isSome_bind h) := by
  cases x <;> trivial

@[grind =] theorem any_bind {p : β → Bool} {f : α → Option β} {o : Option α} :
    (o.bind f).any p = o.any (Option.any p ∘ f) := by
  cases o <;> simp

@[grind =] theorem all_bind {p : β → Bool} {f : α → Option β} {o : Option α} :
    (o.bind f).all p = o.all (Option.all p ∘ f) := by
  cases o <;> simp

@[grind =] theorem bind_id_eq_join {x : Option (Option α)} : x.bind id = x.join := rfl

theorem join_eq_some_iff : x.join = some a ↔ x = some (some a) := by
  simp [← bind_id_eq_join, bind_eq_some_iff]

@[deprecated join_eq_some_iff (since := "2025-04-10")]
abbrev join_eq_some := @join_eq_some_iff

theorem join_ne_none : x.join ≠ none ↔ ∃ z, x = some (some z) := by
  simp only [ne_none_iff_exists', join_eq_some_iff, iff_self]

theorem join_ne_none' : ¬x.join = none ↔ ∃ z, x = some (some z) :=
  join_ne_none

theorem join_eq_none_iff : o.join = none ↔ o = none ∨ o = some none :=
  match o with | none | some none | some (some _) => by simp

@[deprecated join_eq_none_iff (since := "2025-04-10")]
abbrev join_eq_none := @join_eq_none_iff

theorem bind_join {f : α → Option β} {o : Option (Option α)} :
    o.join.bind f = o.bind (·.bind f) := by
  cases o <;> simp

@[simp] theorem map_eq_map : Functor.map f = Option.map f := rfl

@[grind =] theorem map_apply : Functor.map f x = Option.map f x := rfl

@[deprecated map_none (since := "2025-04-10")]
abbrev map_none' := @map_none

@[deprecated map_some (since := "2025-04-10")]
abbrev map_some' := @map_some

@[simp] theorem map_eq_some_iff : x.map f = some b ↔ ∃ a, x = some a ∧ f a = b := by
  cases x <;> simp

@[deprecated map_eq_some_iff (since := "2025-04-10")]
abbrev map_eq_some := @map_eq_some_iff

@[deprecated map_eq_some_iff (since := "2025-04-10")]
abbrev map_eq_some' := @map_eq_some_iff

@[simp] theorem map_eq_none_iff : x.map f = none ↔ x = none := by
  cases x <;> simp [map_none, map_some]

@[deprecated map_eq_none_iff (since := "2025-04-10")]
abbrev map_eq_none := @map_eq_none_iff

@[deprecated map_eq_none_iff (since := "2025-04-10")]
abbrev map_eq_none' := @map_eq_none_iff

@[simp, grind =] theorem isSome_map {x : Option α} : (x.map f).isSome = x.isSome := by
  cases x <;> simp

@[deprecated isSome_map (since := "2025-04-10")]
abbrev isSome_map' := @isSome_map

@[simp, grind =] theorem isNone_map {x : Option α} : (x.map f).isNone = x.isNone := by
  cases x <;> simp

theorem map_eq_bind {x : Option α} : x.map f = x.bind (some ∘ f) := by
  cases x <;> simp [Option.bind]

theorem map_congr {x : Option α} (h : ∀ a, x = some a → f a = g a) :
    x.map f = x.map g := by
  cases x <;> simp only [map_none, map_some, h]

@[simp] theorem map_id_fun {α : Type u} : Option.map (id : α → α) = id := by
  funext; simp [map_id]

@[grind =] theorem map_id_apply {α : Type u} {x : Option α} : Option.map (id : α → α) x = x := by simp

theorem map_id' {x : Option α} : (x.map fun a => a) = x := congrFun map_id x

@[simp] theorem map_id_fun' {α : Type u} : Option.map (fun (a : α) => a) = id := by
  funext; simp [map_id']

theorem map_id_apply' {α : Type u} {x : Option α} : Option.map (fun (a : α) => a) x = x := by simp

@[simp, grind =] theorem get_map {f : α → β} {o : Option α} {h : (o.map f).isSome} :
    (o.map f).get h = f (o.get (by simpa using h)) := by
  cases o with
  | none => simp at h
  | some a => simp

@[simp] theorem map_map (h : β → γ) (g : α → β) (x : Option α) :
    (x.map g).map h = x.map (h ∘ g) := by
  cases x <;> simp only [map_none, map_some, ·∘·]

theorem comp_map (h : β → γ) (g : α → β) (x : Option α) : x.map (h ∘ g) = (x.map g).map h :=
  (map_map ..).symm

@[simp] theorem map_comp_map (f : α → β) (g : β → γ) :
    Option.map g ∘ Option.map f = Option.map (g ∘ f) := by funext x; simp

theorem mem_map_of_mem (g : α → β) (h : a ∈ x) : g a ∈ Option.map g x := h.symm ▸ map_some ..

theorem map_inj_right {f : α → β} {o o' : Option α} (w : ∀ x y, f x = f y → x = y) :
    o.map f = o'.map f ↔ o = o' := by
  cases o with
  | none => cases o' <;> simp
  | some a =>
    cases o' with
    | none => simp
    | some a' => simpa using ⟨fun h => w _ _ h, fun h => congrArg f h⟩

@[simp] theorem map_if {f : α → β} {_ : Decidable c} :
     (if c then some a else none).map f = if c then some (f a) else none := by
  split <;> rfl

@[simp] theorem map_dif {f : α → β} {_ : Decidable c} {a : c → α} :
     (if h : c then some (a h) else none).map f = if h : c then some (f (a h)) else none := by
  split <;> rfl

@[simp, grind =] theorem filter_none (p : α → Bool) : none.filter p = none := rfl

@[grind =] theorem filter_some : Option.filter p (some a) = if p a then some a else none := rfl

theorem filter_some_pos (h : p a) : Option.filter p (some a) = some a := by
  rw [filter_some, if_pos h]

theorem filter_some_neg (h : p a = false) : Option.filter p (some a) = none := by
  rw [filter_some, if_neg] <;> simpa

theorem isSome_of_isSome_filter (p : α → Bool) (o : Option α) (h : (o.filter p).isSome) :
    o.isSome := by
  cases o <;> simp at h ⊢

@[deprecated isSome_of_isSome_filter (since := "2025-03-18")]
abbrev isSome_filter_of_isSome := @isSome_of_isSome_filter

@[simp] theorem filter_eq_none_iff {o : Option α} {p : α → Bool} :
    o.filter p = none ↔ ∀ a, o = some a → ¬ p a := by
  cases o <;> simp [filter_some]

@[deprecated filter_eq_none_iff (since := "2025-04-10")]
abbrev filter_eq_none := @filter_eq_none_iff

@[simp] theorem filter_eq_some_iff {o : Option α} {p : α → Bool} :
    o.filter p = some a ↔ o = some a ∧ p a := by
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

@[deprecated filter_eq_some_iff (since := "2025-04-10")]
abbrev filter_eq_some := @filter_eq_some_iff

theorem filter_some_eq_some : Option.filter p (some a) = some a ↔ p a := by simp

theorem filter_some_eq_none : Option.filter p (some a) = none ↔ ¬p a := by simp

@[grind =]
theorem mem_filter_iff {p : α → Bool} {a : α} {o : Option α} :
    a ∈ o.filter p ↔ a ∈ o ∧ p a := by
  simp

@[grind =]
theorem bind_guard (x : Option α) (p : α → Bool) :
    x.bind (Option.guard p) = x.filter p := by
  cases x <;> rfl

@[deprecated bind_guard (since := "2025-05-15")]
theorem filter_eq_bind (x : Option α) (p : α → Bool) :
    x.filter p = x.bind (Option.guard p) :=
  (bind_guard x p).symm

@[simp, grind =] theorem any_filter : (o : Option α) →
    (Option.filter p o).any q = Option.any (fun a => p a && q a) o
  | none => rfl
  | some a =>
    match h : p a with
    | false => by simp [filter_some_neg h, h]
    | true => by simp [filter_some_pos h, h]

@[simp, grind =] theorem all_filter : (o : Option α) →
    (Option.filter p o).all q = Option.all (fun a => !p a || q a) o
  | none => rfl
  | some a =>
    match h : p a with
    | false => by simp [filter_some_neg h, h]
    | true => by simp [filter_some_pos h, h]

@[simp, grind =] theorem isNone_filter :
    Option.isNone (Option.filter p o) = Option.all (fun a => !p a) o :=
  match o with
  | none => rfl
  | some a =>
    match h : p a with
    | false => by simp [filter_some_neg h, h]
    | true => by simp [filter_some_pos h, h]

@[simp, grind =] theorem isSome_filter : Option.isSome (Option.filter p o) = Option.any p o :=
  match o with
  | none => rfl
  | some a =>
    match h : p a with
    | false => by simp [filter_some_neg h, h]
    | true => by simp [filter_some_pos h, h]

@[simp] theorem filter_filter :
    Option.filter q (Option.filter p o) = Option.filter (fun x => p x && q x) o := by
  cases o <;> repeat (simp_all [filter_some]; try split)

@[grind =] theorem filter_bind {f : α → Option β} :
    (Option.bind x f).filter p = (x.filter (fun a => (f a).any p)).bind f := by
  cases x with
  | none => simp
  | some a =>
    simp only [bind_some, filter_some]
    cases h : f a with
    | none => simp
    | some b =>
      simp only [any_some, filter_some]
      split <;> simp [h]

theorem eq_some_of_filter_eq_some {o : Option α} {a : α} (h : o.filter p = some a) : o = some a :=
  filter_eq_some_iff.1 h |>.1

@[grind =] theorem filter_map {f : α → β} {p : β → Bool} :
    (Option.map f x).filter p = (x.filter (p ∘ f)).map f := by
  cases x <;> simp [filter_some]

@[simp] theorem all_guard (a : α) :
    Option.all q (guard p a) = (!p a || q a) := by
  simp only [guard]
  split <;> simp_all

@[simp] theorem any_guard (a : α) : Option.any q (guard p a) = (p a && q a) := by
  simp only [guard]
  split <;> simp_all

theorem all_eq_true (p : α → Bool) (x : Option α) :
    x.all p = true ↔ ∀ y, x = some y → p y := by
  cases x <;> simp

theorem all_eq_true_iff_get (p : α → Bool) (x : Option α) :
    x.all p = true ↔ (h : x.isSome) → p (x.get h) := by
  cases x <;> simp

theorem all_eq_false (p : α → Bool) (x : Option α) :
    x.all p = false ↔ ∃ y, x = some y ∧ p y = false := by
  cases x <;> simp

theorem all_eq_false_iff_get (p : α → Bool) (x : Option α) :
    x.all p = false ↔ ∃ h : x.isSome, p (x.get h) = false := by
  cases x <;> simp

theorem any_eq_true (p : α → Bool) (x : Option α) :
    x.any p = true ↔ ∃ y, x = some y ∧ p y := by
  cases x <;> simp

theorem any_eq_true_iff_get (p : α → Bool) (x : Option α) :
    x.any p = true ↔ ∃ h : x.isSome, p (x.get h) := by
  cases x <;> simp

theorem any_eq_false (p : α → Bool) (x : Option α) :
    x.any p = false ↔ ∀ y, x = some y → p y = false := by
  cases x <;> simp

theorem any_eq_false_iff_get (p : α → Bool) (x : Option α) :
    x.any p = false ↔ (h : x.isSome) → p (x.get h) = false := by
  cases x <;> simp

theorem isSome_of_any {x : Option α} {p : α → Bool} (h : x.any p) : x.isSome := by
  cases x <;> trivial

theorem get_of_any_eq_true (p : α → Bool) (x : Option α) (h : x.any p = true) :
    p (x.get (isSome_of_any h)) :=
  any_eq_true_iff_get p x |>.1 h |>.2

@[grind =]
theorem any_map {α β : Type _} {x : Option α} {f : α → β} {p : β → Bool} :
    (x.map f).any p = x.any (fun a => p (f a)) := by
  cases x <;> rfl

@[grind =]
theorem all_map {α β : Type _} {x : Option α} {f : α → β} {p : β → Bool} :
    (x.map f).all p = x.all (fun a => p (f a)) := by
  cases x <;> rfl

theorem bind_map_comm {α β} {x : Option (Option α)} {f : α → β} :
    x.bind (Option.map f) = (x.map (Option.map f)).bind id := by cases x <;> simp

@[grind =] theorem bind_map {f : α → β} {g : β → Option γ} {x : Option α} :
    (x.map f).bind g = x.bind (g ∘ f) := by cases x <;> simp

@[simp, grind =] theorem map_bind {f : α → Option β} {g : β → γ} {x : Option α} :
    (x.bind f).map g = x.bind (Option.map g ∘ f) := by cases x <;> simp

@[grind =] theorem join_map_eq_map_join {f : α → β} {x : Option (Option α)} :
    (x.map (Option.map f)).join = x.join.map f := by cases x <;> simp

@[grind _=_] theorem join_join {x : Option (Option (Option α))} : x.join.join = (x.map join).join := by
  cases x <;> simp

theorem mem_of_mem_join {a : α} {x : Option (Option α)} (h : a ∈ x.join) : some a ∈ x :=
  h.symm ▸ join_eq_some_iff.1 h

@[grind _=_] theorem any_join {p : α → Bool} {x : Option (Option α)} :
    x.join.any p = x.any (Option.any p) := by
  cases x <;> simp

@[grind _=_] theorem all_join {p : α → Bool} {x : Option (Option α)} :
    x.join.all p = x.all (Option.all p) := by
  cases x <;> simp

@[grind =] theorem isNone_join {x : Option (Option α)} : x.join.isNone = x.all Option.isNone := by
  cases x <;> simp

@[grind =]theorem isSome_join {x : Option (Option α)} : x.join.isSome = x.any Option.isSome := by
  cases x <;> simp

@[grind =] theorem get_join {x : Option (Option α)} {h} : x.join.get h =
    (x.get (Option.isSome_of_any (Option.isSome_join ▸ h))).get (get_of_any_eq_true _ _ (Option.isSome_join ▸ h)) := by
  cases x with
  | none => simp at h
  | some _ => simp

theorem join_eq_get {x : Option (Option α)} {h} : x.join = x.get h := by
  cases x with
  | none => simp at h
  | some _ => simp

@[grind =] theorem getD_join {x : Option (Option α)} {default : α} :
    x.join.getD default = (x.getD (some default)).getD default := by
  cases x <;> simp

@[grind =] theorem get!_join [Inhabited α] {x : Option (Option α)} :
    x.join.get! = x.get!.get! := by
  cases x <;> simp [default_eq_none]

@[simp] theorem guard_eq_some_iff : guard p a = some b ↔ a = b ∧ p a :=
  if h : p a then by simp [Option.guard, h] else by simp [Option.guard, h]

@[deprecated guard_eq_some_iff (since := "2025-04-10")]
abbrev guard_eq_some := @guard_eq_some_iff

@[simp, grind =] theorem isSome_guard : (Option.guard p a).isSome = p a :=
  if h : p a then by simp [Option.guard, h] else by simp [Option.guard, h]

@[deprecated isSome_guard (since := "2025-03-18")]
abbrev guard_isSome := @isSome_guard

@[simp, grind =] theorem isNone_guard : (Option.guard p a).isNone = !p a := by
  rw [← not_isSome, isSome_guard]

@[simp] theorem guard_eq_none_iff : Option.guard p a = none ↔ p a = false :=
  if h : p a then by simp [Option.guard, h] else by simp [Option.guard, h]

@[simp] theorem guard_pos (h : p a) : Option.guard p a = some a := by
  simp [Option.guard, h]

@[congr] theorem guard_congr {f g : α → Bool} (h : ∀ a, f a = g a) : guard f = guard g := by
  funext a
  simp [guard, h]

@[simp] theorem guard_false {α} :
    guard (fun (_ : α) => false) = fun _ => none := by
  funext a
  simp [guard]

@[simp] theorem guard_true {α} :
    guard (fun (_ : α) => true) = some := by
  funext a
  simp [guard]

theorem guard_comp {p : α → Bool} {f : β → α} :
    guard p ∘ f = Option.map f ∘ guard (p ∘ f) := by
  ext1 b
  simp [guard]

theorem get_none (a : α) {h} : none.get h = a := by
  simp at h

@[simp]
theorem get_none_eq_iff_true {h} : (none : Option α).get h = a ↔ True := by
  simp at h

@[simp, grind =] theorem get_guard : (guard p a).get h = a := by
  simp only [guard]
  split <;> simp

@[grind =] theorem getD_guard : (guard p a).getD b = if p a then a else b := by
  simp only [guard]
  split <;> simp

theorem guard_def (p : α → Bool) :
    Option.guard p = fun x => if p x then some x else none := rfl

@[grind =] theorem guard_apply : Option.guard p x = if p x then some x else none := rfl

@[deprecated guard_def (since := "2025-05-15")]
theorem guard_eq_map (p : α → Bool) :
    Option.guard p = fun x => Option.map (fun _ => x) (if p x then some x else none) := by
  funext x
  simp [Option.guard]

theorem guard_eq_ite {p : α → Bool} {x : α} :
    Option.guard p x = if p x then some x else none := rfl

theorem guard_eq_filter {p : α → Bool} {x : α} :
    Option.guard p x = Option.filter p (some x) := rfl

@[simp] theorem filter_guard {p q : α → Bool} {x : α} :
    (Option.guard p x).filter q = Option.guard (fun y => p y && q y) x := by
  rw [guard_eq_ite]
  split <;> simp_all [filter_some, guard_eq_ite]

theorem map_guard {p : α → Bool} {f : α → β} {x : α} :
    (Option.guard p x).map f = if p x then some (f x) else none := by
  simp [guard_eq_ite]

@[grind =] theorem join_filter {p : Option α → Bool} : {o : Option (Option α)} →
    (o.filter p).join = o.join.filter (fun a => p (some a))
  | none => by simp
  | some none => by
    simp only [join_some, filter_some]
    split <;> simp
  | some (some a) => by
    simp only [join_some, filter_some]
    split <;> simp

@[grind =] theorem filter_join {p : α → Bool} : {o : Option (Option α)} →
    o.join.filter p = (o.filter (Option.any p)).join
  | none => by simp
  | some none => by
    simp only [join_some, filter_some]
    split <;> simp
  | some (some a) => by
    simp only [join_some, filter_some, any_some]
    split <;> simp

theorem merge_eq_or_eq {f : α → α → α} (h : ∀ a b, f a b = a ∨ f a b = b) :
    ∀ o₁ o₂, merge f o₁ o₂ = o₁ ∨ merge f o₁ o₂ = o₂
  | none, none => .inl rfl
  | some _, none => .inl rfl
  | none, some _ => .inr rfl
  | some a, some b => by have := h a b; simp [merge] at this ⊢; exact this

@[simp, grind =] theorem merge_none_left {f} {b : Option α} : merge f none b = b := by
  cases b <;> rfl

@[simp, grind =] theorem merge_none_right {f} {a : Option α} : merge f a none = a := by
  cases a <;> rfl

@[simp, grind =] theorem merge_some_some {f} {a b : α} :
  merge f (some a) (some b) = some (f a b) := rfl

@[deprecated merge_eq_or_eq (since := "2025-04-04")]
theorem liftOrGet_eq_or_eq {f : α → α → α} (h : ∀ a b, f a b = a ∨ f a b = b) :
    ∀ o₁ o₂, merge f o₁ o₂ = o₁ ∨ merge f o₁ o₂ = o₂ :=
  merge_eq_or_eq h

@[deprecated merge_none_left (since := "2025-04-04")]
theorem liftOrGet_none_left {f} {b : Option α} : merge f none b = b :=
  merge_none_left

@[deprecated merge_none_right (since := "2025-04-04")]
theorem liftOrGet_none_right {f} {a : Option α} : merge f a none = a :=
  merge_none_right

@[deprecated merge_some_some (since := "2025-04-04")]
theorem liftOrGet_some_some {f} {a b : α} : merge f (some a) (some b) = some (f a b) :=
  merge_some_some

instance commutative_merge (f : α → α → α) [Std.Commutative f] :
    Std.Commutative (merge f) :=
  ⟨fun a b ↦ by cases a <;> cases b <;> simp [merge, Std.Commutative.comm]⟩

instance associative_merge (f : α → α → α) [Std.Associative f] :
    Std.Associative (merge f) :=
  ⟨fun a b c ↦ by cases a <;> cases b <;> cases c <;> simp [merge, Std.Associative.assoc]⟩

instance idempotentOp_merge (f : α → α → α) [Std.IdempotentOp f] :
    Std.IdempotentOp (merge f) :=
  ⟨fun a ↦ by cases a <;> simp [merge, Std.IdempotentOp.idempotent]⟩

instance lawfulIdentity_merge (f : α → α → α) : Std.LawfulIdentity (merge f) none where
  left_id a := by cases a <;> simp [merge]
  right_id a := by cases a <;> simp [merge]

theorem merge_join {o o' : Option (Option α)} {f : α → α → α} :
    o.join.merge f o'.join = (o.merge (Option.merge f) o').join := by
  cases o <;> cases o' <;> simp

theorem merge_eq_some_iff {o o' : Option α} {f : α → α → α} {a : α} :
    o.merge f o' = some a ↔ (o = some a ∧ o' = none) ∨ (o = none ∧ o' = some a) ∨
      (∃ b c, o = some b ∧ o' = some c ∧ f b c = a) := by
  cases o <;> cases o' <;> simp

@[simp]
theorem merge_eq_none_iff {o o' : Option α} : o.merge f o' = none ↔ o = none ∧ o' = none := by
  cases o <;> cases o' <;> simp

@[simp, grind =]
theorem any_merge {p : α → Bool} {f : α → α → α} (hpf : ∀ a b, p (f a b) = (p a || p b))
    {o o' : Option α} : (o.merge f o').any p = (o.any p || o'.any p) := by
  cases o <;> cases o' <;> simp [*]

@[simp, grind =]
theorem all_merge {p : α → Bool} {f : α → α → α} (hpf : ∀ a b, p (f a b) = (p a && p b))
    {o o' : Option α} : (o.merge f o').all p = (o.all p && o'.all p) := by
  cases o <;> cases o' <;> simp [*]

@[simp, grind =]
theorem isSome_merge {o o' : Option α} {f : α → α → α} :
    (o.merge f o').isSome = (o.isSome || o'.isSome) := by
  simp [← any_true]

@[simp, grind =]
theorem isNone_merge {o o' : Option α} {f : α → α → α} :
    (o.merge f o').isNone = (o.isNone && o'.isNone) := by
  simp [← all_false]

@[simp]
theorem get_merge {o o' : Option α} {f : α → α → α} {i : α} [Std.LawfulIdentity f i] {h} :
    (o.merge f o').get h = f (o.getD i) (o'.getD i) := by
  cases o <;> cases o' <;> simp [Std.LawfulLeftIdentity.left_id, Std.LawfulRightIdentity.right_id]

@[simp, grind =] theorem elim_none (x : β) (f : α → β) : Option.elim none x f = x := rfl

@[simp, grind =] theorem elim_some (x : β) (f : α → β) (a : α) : (some a).elim x f = f a := rfl

@[grind =] theorem elim_filter {o : Option α} {b : β} :
    Option.elim (Option.filter p o) b f = Option.elim o b (fun a => if p a then f a else b) :=
  match o with
  | none => rfl
  | some a =>
    match h : p a with
    | false => by simp [filter_some_neg h, h]
    | true => by simp [filter_some_pos, h]

@[grind =] theorem elim_join {o : Option (Option α)} {b : β} {f : α → β} :
    o.join.elim b f = o.elim b (·.elim b f) := by
  cases o <;> simp

theorem elim_guard : (guard p a).elim b f = if p a then f a else b := by
  cases h : p a <;> simp [*, guard]

-- I don't see how to construct a good grind pattern to instantiate this.
@[simp] theorem getD_map (f : α → β) (x : α) (o : Option α) :
  (o.map f).getD (f x) = f (getD o x) := by cases o <;> rfl

section choice

attribute [local instance] Classical.propDecidable

/--
An optional arbitrary element of a given type.

If `α` is non-empty, then there exists some `v : α` and this arbitrary element is `some v`.
Otherwise, it is `none`.
-/
noncomputable def choice (α : Type _) : Option α :=
  if h : Nonempty α then some (Classical.choice h) else none

theorem choice_eq_some [Subsingleton α] (a : α) : choice α = some a := by
  simp [choice]
  rw [dif_pos (⟨a⟩ : Nonempty α)]
  simp; apply Subsingleton.elim

@[deprecated choice_eq_some (since := "2025-05-12")]
abbrev choice_eq := @choice_eq_some

@[simp]
theorem choice_eq_default [Subsingleton α] [Inhabited α] : choice α = some default :=
  choice_eq_some _

theorem choice_eq_none_iff_not_nonempty : choice α = none ↔ ¬Nonempty α := by
  simp [choice]

theorem isNone_choice_iff_not_nonempty : (choice α).isNone ↔ ¬Nonempty α := by
  rw [isNone_iff_eq_none, choice_eq_none_iff_not_nonempty]

grind_pattern isNone_choice_iff_not_nonempty => (choice α).isNone

theorem isSome_choice_iff_nonempty : (choice α).isSome ↔ Nonempty α :=
  ⟨fun h => ⟨(choice α).get h⟩, fun h => by simp only [choice, dif_pos h, isSome_some]⟩

grind_pattern isSome_choice_iff_nonempty => (choice α).isSome

@[simp]
theorem isSome_choice [Nonempty α] : (choice α).isSome :=
  isSome_choice_iff_nonempty.2 inferInstance

@[deprecated isSome_choice_iff_nonempty (since := "2025-03-18")]
abbrev choice_isSome_iff_nonempty := @isSome_choice_iff_nonempty

@[simp]
theorem isNone_choice_eq_false [Nonempty α] : (choice α).isNone = false := by
  simp [← not_isSome]

@[simp, grind =]
theorem getD_choice {a} :
    (choice α).getD a = (choice α).get (isSome_choice_iff_nonempty.2 ⟨a⟩) := by
  rw [get_eq_getD]

@[simp, grind =]
theorem get!_choice [Inhabited α] : (choice α).get! = (choice α).get isSome_choice := by
  rw [get_eq_get!]

end choice

@[simp, grind =] theorem toList_some (a : α) : (some a).toList = [a] := rfl
@[simp, grind =] theorem toList_none (α : Type _) : (none : Option α).toList = [] := rfl

@[simp, grind =] theorem toArray_some (a : α) : (some a).toArray = #[a] := rfl
@[simp, grind =] theorem toArray_none (α : Type _) : (none : Option α).toArray = #[] := rfl

-- See `Init.Data.Option.List` for lemmas about `toList`.

@[simp, grind =] theorem some_or : (some a).or o = some a := rfl
@[simp, grind =] theorem none_or : none.or o = o := rfl

theorem or_eq_right_of_none {o o' : Option α} (h : o = none) : o.or o' = o' := by
  cases h; simp

@[simp, grind =] theorem or_some {o : Option α} : o.or (some a) = some (o.getD a) := by
  cases o <;> rfl

@[deprecated or_some (since := "2025-05-03")]
abbrev or_some' := @or_some

@[simp, grind =]
theorem or_none : or o none = o := by
  cases o <;> rfl

theorem or_eq_bif : or o o' = bif o.isSome then o else o' := by
  cases o <;> rfl

@[simp, grind =] theorem isSome_or : (or o o').isSome = (o.isSome || o'.isSome) := by
  cases o <;> rfl

@[simp, grind =] theorem isNone_or : (or o o').isNone = (o.isNone && o'.isNone) := by
  cases o <;> rfl

@[simp] theorem or_eq_none_iff : or o o' = none ↔ o = none ∧ o' = none := by
  cases o <;> simp

@[deprecated or_eq_none_iff (since := "2025-04-10")]
abbrev or_eq_none := @or_eq_none_iff

@[simp] theorem or_eq_some_iff : or o o' = some a ↔ o = some a ∨ (o = none ∧ o' = some a) := by
  cases o <;> simp

@[deprecated or_eq_some_iff (since := "2025-04-10")]
abbrev or_eq_some := @or_eq_some_iff

@[grind _=_] theorem or_assoc : or (or o₁ o₂) o₃ = or o₁ (or o₂ o₃) := by
  cases o₁ <;> cases o₂ <;> rfl
instance : Std.Associative (or (α := α)) := ⟨@or_assoc _⟩

theorem or_eq_left_of_none {o o' : Option α} (h : o' = none) : o.or o' = o := by
  cases h; simp

instance : Std.LawfulIdentity (or (α := α)) none where
  left_id := @none_or _
  right_id := @or_none _

@[simp, grind =]
theorem or_self : or o o = o := by
  cases o <;> rfl
instance : Std.IdempotentOp (or (α := α)) := ⟨@or_self _⟩

@[grind _=_] theorem map_or : (or o o').map f = (o.map f).or (o'.map f) := by
  cases o <;> rfl

@[deprecated map_or (since := "2025-04-10")]
abbrev map_or' := @map_or

theorem or_of_isSome {o o' : Option α} (h : o.isSome) : o.or o' = o := by
  match o, h with
  | some _, _ => simp

theorem or_of_isNone {o o' : Option α} (h : o.isNone) : o.or o' = o' := by
  match o, h with
  | none, _ => simp

@[simp, grind =]
theorem getD_or {o o' : Option α} {fallback : α} :
    (o.or o').getD fallback = o.getD (o'.getD fallback) := by
  cases o <;> simp

@[simp, grind =]
theorem get!_or {o o' : Option α} [Inhabited α] : (o.or o').get! = o.getD o'.get! := by
  cases o <;> simp

@[simp, grind =] theorem filter_or_filter {o o' : Option α} {f : α → Bool} :
    (o.or (o'.filter f)).filter f = (o.or o').filter f := by
  cases o <;> cases o' <;> simp

theorem guard_or_guard : (guard p a).or (guard q a) = guard (fun x => p x || q x) a := by
  simp only [guard]
  split <;> simp_all

/-! ### `orElse` -/

/-- The `simp` normal form of `o <|> o'` is `o.or o'` via `orElse_eq_orElse` and `orElse_eq_or`. -/
@[simp] theorem orElse_eq_orElse : HOrElse.hOrElse = @Option.orElse α := rfl

@[grind =] theorem orElse_apply : HOrElse.hOrElse o o' = Option.orElse o o' := rfl

theorem or_eq_orElse : or o o' = o.orElse (fun _ => o') := by
  cases o <;> rfl

/-- The `simp` normal form of `o.orElse f` is o.or (f ())`. -/
@[simp, grind =] theorem orElse_eq_or {o : Option α} {f} : o.orElse f = o.or (f ()) := by
  simp [or_eq_orElse]

@[deprecated or_some (since := "2025-05-03")]
theorem some_orElse (a : α) (f) : (some a).orElse f = some a := rfl

@[deprecated or_none (since := "2025-05-03")]
theorem none_orElse (f : Unit → Option α) : none.orElse f = f () := rfl

@[deprecated or_none (since := "2025-05-13")]
theorem orElse_fun_none (x : Option α) : x.orElse (fun _ => none) = x := by simp

@[deprecated or_some (since := "2025-05-13")]
theorem orElse_fun_some (x : Option α) (a : α) :
    x.orElse (fun _ => some a) = some (x.getD a) := by simp

@[deprecated or_eq_some_iff (since := "2025-05-13")]
theorem orElse_eq_some_iff (o : Option α) (f) (x : α) :
    (o.orElse f) = some x ↔ o = some x ∨ o = none ∧ f () = some x := by simp

@[deprecated or_eq_none_iff (since := "2025-05-13")]
theorem orElse_eq_none_iff (o : Option α) (f) : (o.orElse f) = none ↔ o = none ∧ f () = none := by simp

@[deprecated map_or (since := "2025-05-13")]
theorem map_orElse {x : Option α} {y} :
    (x.orElse y).map f = (x.map f).orElse (fun _ => (y ()).map f) := by simp [map_or]

/-! ### beq -/

section beq

variable [BEq α]

@[simp, grind =] theorem none_beq_none : ((none : Option α) == none) = true := rfl
@[simp, grind =] theorem none_beq_some (a : α) : ((none : Option α) == some a) = false := rfl
@[simp, grind =] theorem some_beq_none (a : α) : ((some a : Option α) == none) = false := rfl
@[simp, grind =] theorem some_beq_some {a b : α} : (some a == some b) = (a == b) := rfl

/-- We simplify away `isEqSome` in terms of `==`. -/
@[simp, grind =] theorem isEqSome_eq_beq_some {o : Option α} : isEqSome o y = (o == some y) := by
  cases o <;> simp [isEqSome]

@[simp] theorem reflBEq_iff : ReflBEq (Option α) ↔ ReflBEq α := by
  constructor
  · intro h
    constructor
    intro a
    suffices (some a == some a) = true by
      simpa only [some_beq_some]
    simp
  · intro h
    infer_instance

@[simp] theorem lawfulBEq_iff : LawfulBEq (Option α) ↔ LawfulBEq α := by
  constructor
  · intro h
    have : ReflBEq α := reflBEq_iff.mp inferInstance
    constructor
    intro a b h
    apply Option.some.inj
    apply eq_of_beq
    simpa
  · intro h
    infer_instance

@[simp] theorem beq_none {o : Option α} : (o == none) = o.isNone := by cases o <;> simp

@[simp, grind =]
theorem filter_beq_self [ReflBEq α] {p : α → Bool} {o : Option α} : (o.filter p == o) = o.all p := by
  cases o with
  | none => simp
  | some _ =>
    simp only [filter_some]
    split <;> simp [*]

@[simp, grind =]
theorem self_beq_filter [ReflBEq α] {p : α → Bool} {o : Option α} : (o == o.filter p) = o.all p := by
  cases o with
  | none => simp
  | some _ =>
    simp only [filter_some]
    split <;> simp [*]

theorem join_beq_some {o : Option (Option α)} {a : α} : (o.join == some a) = (o == some (some a)) := by
  cases o <;> simp

theorem join_beq_none {o : Option (Option α)} : (o.join == none) = (o == none || o == some none) := by
  cases o <;> simp

@[simp]
theorem guard_beq_some [ReflBEq α] {x : α} {p : α → Bool} : (guard p x == some x) = p x := by
  simp only [guard_eq_ite]
  split <;> simp [*]

theorem guard_beq_none {x : α} {p : α → Bool} : (guard p x == none) = !p x := by
  simp

theorem merge_beq_none {o o' : Option α} {f : α → α → α} :
    (o.merge f o' == none) = (o == none && o' == none) := by
  simp [beq_none]

end beq

/-! ### ite -/
section ite

@[simp] theorem dite_none_left_eq_some {p : Prop} {_ : Decidable p} {b : ¬p → Option β} :
    (if h : p then none else b h) = some a ↔ ∃ h, b h = some a := by
  split <;> simp_all

@[simp] theorem dite_none_right_eq_some {p : Prop} {_ : Decidable p} {b : p → Option α} :
    (if h : p then b h else none) = some a ↔ ∃ h, b h = some a := by
  split <;> simp_all

@[simp] theorem some_eq_dite_none_left {p : Prop} {_ : Decidable p} {b : ¬p → Option β} :
    some a = (if h : p then none else b h) ↔ ∃ h, some a = b h := by
  split <;> simp_all

@[simp] theorem some_eq_dite_none_right {p : Prop} {_ : Decidable p} {b : p → Option α} :
    some a = (if h : p then b h else none) ↔ ∃ h, some a = b h := by
  split <;> simp_all

@[simp] theorem ite_none_left_eq_some {p : Prop} {_ : Decidable p} {b : Option β} :
    (if p then none else b) = some a ↔ ¬ p ∧ b = some a := by
  split <;> simp_all

@[simp] theorem ite_none_right_eq_some {p : Prop} {_ : Decidable p} {b : Option α} :
    (if p then b else none) = some a ↔ p ∧ b = some a := by
  split <;> simp_all

@[simp] theorem some_eq_ite_none_left {p : Prop} {_ : Decidable p} {b : Option β} :
    some a = (if p then none else b) ↔ ¬ p ∧ some a = b := by
  split <;> simp_all

@[simp] theorem some_eq_ite_none_right {p : Prop} {_ : Decidable p} {b : Option α} :
    some a = (if p then b else none) ↔ p ∧ some a = b := by
  split <;> simp_all

theorem ite_some_none_eq_some {p : Prop} {_ : Decidable p} {a b : α} :
    (if p then some a else none) = some b ↔ p ∧ a = b := by simp

theorem mem_dite_none_left {x : α} {_ : Decidable p} {l : ¬ p → Option α} :
    (x ∈ if h : p then none else l h) ↔ ∃ h : ¬ p, x ∈ l h := by
  simp

theorem mem_dite_none_right {x : α} {_ : Decidable p} {l : p → Option α} :
    (x ∈ if h : p then l h else none) ↔ ∃ h : p, x ∈ l h := by
  simp

theorem mem_ite_none_left {x : α} {_ : Decidable p} {l : Option α} :
    (x ∈ if p then none else l) ↔ ¬ p ∧ x ∈ l := by
  simp

theorem mem_ite_none_right {x : α} {_ : Decidable p} {l : Option α} :
    (x ∈ if p then l else none) ↔ p ∧ x ∈ l := by
  simp

@[simp] theorem isSome_dite {p : Prop} {_ : Decidable p} {b : p → β} :
    (if h : p then some (b h) else none).isSome = true ↔ p := by
  split <;> simpa

@[simp] theorem isSome_ite {p : Prop} {_ : Decidable p} :
    (if p then some b else none).isSome = true ↔ p := by
  split <;> simpa

@[simp] theorem isSome_dite' {p : Prop} {_ : Decidable p} {b : ¬ p → β} :
    (if h : p then none else some (b h)).isSome = true ↔ ¬ p := by
  split <;> simpa

@[simp] theorem isSome_ite' {p : Prop} {_ : Decidable p} :
    (if p then none else some b).isSome = true ↔ ¬ p := by
  split <;> simpa

@[simp] theorem get_dite {p : Prop} {_ : Decidable p} (b : p → β) (w) :
    (if h : p then some (b h) else none).get w = b (by simpa using w) := by
  split
  · simp
  · exfalso
    simp at w
    contradiction

@[simp] theorem get_ite {p : Prop} {_ : Decidable p} (h) :
    (if p then some b else none).get h = b := by
  simpa using get_dite (p := p) (fun _ => b) (by simpa using h)

@[simp] theorem get_dite' {p : Prop} {_ : Decidable p} (b : ¬ p → β) (w) :
    (if h : p then none else some (b h)).get w = b (by simpa using w) := by
  split
  · exfalso
    simp at w
    contradiction
  · simp

@[simp] theorem get_ite' {p : Prop} {_ : Decidable p} (h) :
    (if p then none else some b).get h = b := by
  simpa using get_dite' (p := p) (fun _ => b) (by simpa using h)

end ite

@[simp, grind =] theorem get_filter {α : Type _} {x : Option α} {f : α → Bool} (h : (x.filter f).isSome) :
    (x.filter f).get h = x.get (isSome_of_isSome_filter f x h) := by
  cases x
  · contradiction
  · unfold Option.filter
    simp only [Option.get_ite, Option.get_some]

/-! ### pbind -/

@[simp] theorem pbind_none : pbind none f = none := rfl
@[simp] theorem pbind_some : pbind (some a) f = f a rfl := rfl

@[grind = gen] theorem pbind_none' (h : x = none) : pbind x f = none := by subst h; rfl
@[grind = gen] theorem pbind_some' (h : x = some a) : pbind x f = f a h := by subst h; rfl

@[simp, grind =] theorem map_pbind {o : Option α} {f : (a : α) → o = some a → Option β}
    {g : β → γ} : (o.pbind f).map g = o.pbind (fun a h => (f a h).map g) := by
  cases o <;> rfl

@[simp, grind =] theorem pbind_map {α β γ : Type _} (o : Option α)
    (f : α → β) (g : (x : β) → o.map f = some x → Option γ) :
    (o.map f).pbind g = o.pbind (fun x h => g (f x) (h ▸ rfl)) := by
  cases o <;> rfl

@[simp] theorem pbind_eq_bind {α β : Type _} (o : Option α)
    (f : α → Option β) : o.pbind (fun x _ => f x) = o.bind f := by
  cases o <;> rfl

@[congr] theorem pbind_congr {o o' : Option α} (ho : o = o')
    {f : (a : α) → o = some a → Option β} {g : (a : α) → o' = some a → Option β}
    (hf : ∀ a h, f a (ho ▸ h) = g a h) : o.pbind f = o'.pbind g := by
  subst ho
  exact (funext fun a => funext fun h => hf a h) ▸ Eq.refl (o.pbind f)

theorem pbind_eq_none_iff {o : Option α} {f : (a : α) → o = some a → Option β} :
    o.pbind f = none ↔ o = none ∨ ∃ a h, f a h = none := by
  cases o <;> simp

theorem isSome_pbind_iff {o : Option α} {f : (a : α) → o = some a → Option β} :
    (o.pbind f).isSome ↔ ∃ a h, (f a h).isSome := by
  cases o <;> simp

theorem isNone_pbind_iff {o : Option α} {f : (a : α) → o = some a → Option β} :
    (o.pbind f).isNone ↔ o = none ∨ ∃ a h, f a h = none := by
  cases o <;> simp

@[deprecated "isSome_pbind_iff" (since := "2025-04-01")]
theorem pbind_isSome {o : Option α} {f : (a : α) → o = some a → Option β} :
    (o.pbind f).isSome = ∃ a h, (f a h).isSome := by
  exact propext isSome_pbind_iff

theorem pbind_eq_some_iff {o : Option α} {f : (a : α) → o = some a → Option β} {b : β} :
    o.pbind f = some b ↔ ∃ a h, f a h = some b := by
  cases o <;> simp

@[grind =] theorem pbind_join {o : Option (Option α)} {f : (a : α) → o.join = some a → Option β} :
    o.join.pbind f = o.pbind (fun o' ho' => o'.pbind (fun a ha => f a (by simp_all))) := by
  cases o <;> simp <;> congr

theorem isSome_of_isSome_pbind {o : Option α} {f : (a : α) → o = some a → Option β} :
    (o.pbind f).isSome → o.isSome := by
  cases o <;> simp

theorem isSome_get_of_isSome_pbind {o : Option α} {f : (a : α) → o = some a → Option β}
    (h : (o.pbind f).isSome) : (f (o.get (isSome_of_isSome_pbind h)) (by simp)).isSome := by
  cases o with
  | none => simp at h
  | some a => simp [← h]

@[simp, grind =]
theorem get_pbind {o : Option α} {f : (a : α) → o = some a → Option β} {h} :
    (o.pbind f).get h = (f (o.get (isSome_of_isSome_pbind h)) (by simp)).get (isSome_get_of_isSome_pbind h) := by
  cases o <;> simp

/-! ### pmap -/

@[simp] theorem pmap_none {p : α → Prop} {f : ∀ (a : α), p a → β} {h} :
    pmap f none h = none := rfl

@[simp] theorem pmap_some {p : α → Prop} {f : ∀ (a : α), p a → β} {h} :
    pmap f (some a) h = some (f a (h a rfl)) := rfl

@[grind = gen] theorem pmap_none' {p : α → Prop} {f : ∀ (a : α), p a → β} (he : x = none) {h} :
    pmap f x h = none := by subst he; rfl

@[grind = gen] theorem pmap_some' {p : α → Prop} {f : ∀ (a : α), p a → β} (he : x = some a) {h} :
    pmap f x h = some (f a (h a he)) := by subst he; rfl

@[simp] theorem pmap_eq_none_iff {p : α → Prop} {f : ∀ (a : α), p a → β} {h} :
    pmap f o h = none ↔ o = none := by
  cases o <;> simp

@[simp, grind =] theorem isSome_pmap {p : α → Prop} {f : ∀ (a : α), p a → β} {o : Option α} {h} :
    (pmap f o h).isSome = o.isSome := by
  cases o <;> simp

@[simp, grind =] theorem isNone_pmap {p : α → Prop} {f : ∀ (a : α), p a → β} {o : Option α} {h} :
    (pmap f o h).isNone = o.isNone := by
  cases o <;> simp

@[deprecated isSome_pmap (since := "2025-04-01")] abbrev pmap_isSome := @isSome_pmap

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

@[simp]
theorem pmap_eq_map (p : α → Prop) (f : α → β) (o : Option α) (H) :
    @pmap _ _ p (fun a _ => f a) o H = Option.map f o := by
  cases o <;> simp

@[grind =] theorem map_pmap {p : α → Prop} (g : β → γ) (f : ∀ a, p a → β) (o H) :
    Option.map g (pmap f o H) = pmap (fun a h => g (f a h)) o H := by
  cases o <;> simp

@[grind =] theorem pmap_map (o : Option α) (f : α → β) {p : β → Prop} (g : ∀ b, p b → γ) (H) :
    pmap g (o.map f) H =
      pmap (fun a h => g (f a) h) o (fun a m => H (f a) (map_eq_some_iff.2 ⟨_, m, rfl⟩)) := by
  cases o <;> simp

theorem pmap_or {p : α → Prop} {f : ∀ (a : α), p a → β} {o o' : Option α} {h} :
    (or o o').pmap f h =
      match o with
      | none => o'.pmap f (fun a h' => h a (by simp [h']))
      | some a => some (f a (h a (by simp))) := by
  cases o <;> simp

theorem pmap_pred_congr {α : Type u}
    {p p' : α → Prop} (hp : ∀ x, p x ↔ p' x)
    {o o' : Option α} (ho : o = o')
    (h : ∀ x, o = some x → p x) : ∀ x, o' = some x → p' x := by
  intro y hy
  cases ho
  exact (hp y).mp (h y hy)

@[congr]
theorem pmap_congr {α : Type u} {β : Type v}
    {p p' : α → Prop} (hp : ∀ x, p x ↔ p' x)
    {f : (x : α) → p x → β} {f' : (x : α) → p' x → β}
    (hf : ∀ x h, f x ((hp x).mpr h) = f' x h)
    {o o' : Option α} (ho : o = o')
    {h : ∀ x, o = some x → p x} :
    Option.pmap f o h = Option.pmap f' o' (Option.pmap_pred_congr hp ho h) := by
  cases ho
  cases o
  · rfl
  · dsimp
    rw [hf]

theorem pmap_guard {q : α → Bool} {p : α → Prop} (f : (x : α) → p x → β) {x : α}
    (h : ∀ (a : α), guard q x = some a → p a) :
    (guard q x).pmap f h = if h' : q x then some (f x (h _ (by simp_all))) else none := by
  simp only [guard_eq_ite]
  split <;> simp_all

@[simp, grind =]
theorem get_pmap {p : α → Bool} {f : (x : α) → p x → β} {o : Option α}
    {h : ∀ a, o = some a → p a} {h'} :
    (o.pmap f h).get h' = f (o.get (by simpa using h')) (h _ (by simp)) := by
  cases o <;> simp

/-! ### pelim -/

@[simp] theorem pelim_none : pelim none b f = b := rfl
@[simp] theorem pelim_some : pelim (some a) b f = f a rfl := rfl

@[grind = gen] theorem pelim_none' (h : x = none) : pelim x b f = b := by subst h; rfl
@[grind = gen] theorem pelim_some' (h : x = some a) : pelim x b f = f a h := by subst h; rfl

@[simp] theorem pelim_eq_elim : pelim o b (fun a _ => f a) = o.elim b f := by
  cases o <;> simp

@[simp, grind =] theorem elim_pmap {p : α → Prop} (f : (a : α) → p a → β) (o : Option α)
    (H : ∀ (a : α), o = some a → p a) (g : γ) (g' : β → γ) :
    (o.pmap f H).elim g g' =
       o.pelim g (fun a h => g' (f a (H a h))) := by
  cases o <;> simp

theorem pelim_congr_left {o o' : Option α } {b : β} {f : (a : α) → (a ∈ o) → β} (h : o = o') :
    pelim o b f = pelim o' b (fun a ha => f a (h ▸ ha)) := by
  cases h; rfl

@[grind =] theorem pelim_filter {o : Option α} {b : β} {f : (a : α) → a ∈ o.filter p → β} :
    Option.pelim (Option.filter p o) b f =
      Option.pelim o b (fun a h => if hp : p a then f a (Option.mem_filter_iff.2 ⟨h, hp⟩) else b) :=
  match o with
  | none => rfl
  | some a =>
    match h : p a with
    | false => by simp [pelim_congr_left (filter_some_neg h), h]
    | true => by simp [pelim_congr_left (filter_some_pos h), h]

@[grind =] theorem pelim_join {o : Option (Option α)} {b : β} {f : (a : α) → a ∈ o.join → β} :
    o.join.pelim b f = o.pelim b (fun o' ho' => o'.pelim b (fun a ha => f a (by simp_all))) := by
  cases o <;> simp <;> congr

@[congr]
theorem pelim_congr {o o' : Option α} {b b' : β}
    {f : (a : α) → o = some a → β} {g : (a : α) → o' = some a → β}
    (ho : o = o') (hb : b = b') (hf : ∀ a ha, f a (ho.trans ha) = g a ha) :
    o.pelim b f = o'.pelim b' g := by
  cases ho; cases hb; cases o <;> apply_assumption

theorem pelim_guard {a : α} {f : (a' : α) → guard p a = some a' → β} :
    (guard p a).pelim b f = if h : p a then f a (by simpa) else b := by
  simp only [guard]
  split <;> simp

/-! ### pfilter -/

@[congr]
theorem pfilter_congr {α : Type u} {o o' : Option α} (ho : o = o')
    {f : (a : α) → o = some a → Bool} {g : (a : α) → o' = some a → Bool}
    (hf : ∀ a ha, f a (ho.trans ha) = g a ha) :
    o.pfilter f = o'.pfilter g := by
  cases ho
  congr; funext a ha
  exact hf a ha

@[simp, grind =] theorem pfilter_none {α : Type _} {p : (a : α) → none = some a → Bool} :
    none.pfilter p = none := by
  rfl

@[simp, grind =] theorem pfilter_some {α : Type _} {x : α} {p : (a : α) → some x = some a → Bool} :
    (some x).pfilter p = if p x rfl then some x else none := by
  simp only [pfilter, cond_eq_if]

theorem isSome_pfilter_iff {α : Type _} {o : Option α} {p : (a : α) → o = some a → Bool} :
    (o.pfilter p).isSome ↔ ∃ (a : α) (ha : o = some a), p a ha := by
  cases o <;> simp

theorem isSome_pfilter_iff_get {α : Type _} {o : Option α} {p : (a : α) → o = some a → Bool} :
    (o.pfilter p).isSome ↔ ∃ (h : o.isSome), p (o.get h) (some_get _).symm := by
  cases o <;> simp

theorem isSome_of_isSome_pfilter {α : Type _} {o : Option α} {p : (a : α) → o = some a → Bool}
    (h : (o.pfilter p).isSome) : o.isSome :=
  (isSome_pfilter_iff_get.mp h).1

theorem isNone_pfilter_iff {o : Option α} {p : (a : α) → o = some a → Bool} :
    (o.pfilter p).isNone ↔ ∀ (a : α) (ha : o = some a), p a ha = false := by
  cases o with
  | none => simp
  | some a =>
    simp only [pfilter_some, isNone_iff_eq_none, ite_eq_right_iff, reduceCtorEq, imp_false,
      Bool.not_eq_true, some.injEq]
    exact ⟨fun h _ h' => h' ▸ h, fun h => h _ rfl⟩

@[simp, grind =] theorem get_pfilter {α : Type _} {o : Option α} {p : (a : α) → o = some a → Bool}
    (h : (o.pfilter p).isSome) :
    (o.pfilter p).get h = o.get (isSome_of_isSome_pfilter h) := by
  cases o <;> simp

theorem pfilter_eq_none_iff {α : Type _} {o : Option α} {p : (a : α) → o = some a → Bool} :
    o.pfilter p = none ↔ o = none ∨ ∃ (a : α) (ha : o = some a), p a ha = false := by
  cases o <;> simp

theorem pfilter_eq_some_iff {α : Type _} {o : Option α} {p : (a : α) → o = some a → Bool}
    {a : α} : o.pfilter p = some a ↔ ∃ ha, p a ha = true := by
  simp only [eq_some_iff_get_eq, get_pfilter, isSome_pfilter_iff]
  constructor
  · rintro ⟨⟨b, ⟨hb, rfl⟩, hb'⟩, rfl⟩
    exact ⟨⟨hb, rfl⟩, hb'⟩
  · rintro ⟨⟨h, rfl⟩, h'⟩
    exact ⟨⟨o.get h, ⟨h, rfl⟩, h'⟩, rfl⟩

theorem eq_some_of_pfilter_eq_some {o : Option α} {p : (a : α) → o = some a → Bool}
    {a : α} (h : o.pfilter p = some a) : o = some a :=
  pfilter_eq_some_iff.1 h |>.1

@[grind =] theorem filter_pbind {f : (a : α) → o = some a → Option β} :
    (Option.pbind o f).filter p =
      (o.pfilter (fun a h => (f a h).any p)).pbind (fun a h => f a (eq_some_of_pfilter_eq_some h)) := by
  cases o with
  | none => simp
  | some a =>
    simp only [pbind_some, pfilter_some]
    obtain (h|⟨b, h⟩) := Option.eq_none_or_eq_some (f a rfl)
    · simp [h]
    · simp only [h, filter_some, any_some]
      split <;> simp [h]

@[simp] theorem pfilter_eq_filter {α : Type _} {o : Option α} {p : α → Bool} :
    o.pfilter (fun a _ => p a) = o.filter p := by
  cases o with
  | none => rfl
  | some a =>
    simp only [pfilter, Option.filter, Bool.cond_eq_ite_iff]

@[simp] theorem pfilter_filter {o : Option α} {p : α → Bool} {q : (a : α) → o.filter p = some a → Bool} :
    (o.filter p).pfilter q = o.pfilter (fun a h => if h' : p a then q a (Option.filter_eq_some_iff.2 ⟨h, h'⟩) else false) := by
  cases o with
  | none => simp
  | some a =>
    simp only [filter_some, pfilter_some]
    split <;> simp

@[simp] theorem filter_pfilter {o : Option α} {p : (a : α) → o = some a → Bool} {q : α → Bool} :
    (o.pfilter p).filter q = o.pfilter (fun a h => p a h && q a) := by
  cases o with
  | none => simp
  | some a =>
    simp only [pfilter_some, Bool.and_eq_true]
    split <;> simp [filter_some, *]

@[simp] theorem pfilter_pfilter {o : Option α} {p : (a : α) → o = some a → Bool}
    {q : (a : α) → o.pfilter p = some a → Bool} :
    (o.pfilter p).pfilter q = o.pfilter (fun a h => if h' : p a h then q a (Option.pfilter_eq_some_iff.2 ⟨h, h'⟩) else false) := by
  cases o with
  | none => simp
  | some a =>
    simp only [pfilter_some]
    split <;> simp

theorem pfilter_eq_pbind_ite {α : Type _} {o : Option α}
    {p : (a : α) → o = some a → Bool} :
    o.pfilter p = o.pbind (fun a h => if p a h then some a else none) := by
  cases o
  · rfl
  · simp only [Option.pfilter, Bool.cond_eq_ite, Option.pbind_some]

@[grind =] theorem filter_pmap {p : α → Prop} {f : (a : α) → p a → β} {h : ∀ (a : α), o = some a → p a}
    {q : β → Bool} : (o.pmap f h).filter q = (o.pfilter (fun a h' => q (f a (h _ h')))).pmap f
      (fun _ h' => h _ (eq_some_of_pfilter_eq_some h')) := by
  cases o with
  | none => simp
  | some a =>
    simp only [pmap_some, filter_some, pfilter_some]
    split <;> simp

@[grind =] theorem pfilter_join {o : Option (Option α)} {p : (a : α) → o.join = some a → Bool} :
    o.join.pfilter p = (o.pfilter (fun o' h => o'.pelim false (fun a ha => p a (by simp_all)))).join := by
  cases o with
  | none => simp
  | some o' =>
    cases o' with
    | none => simp
    | some a =>
      simp only [join_some, pfilter_some, pelim_some]
      split <;> simp

@[grind =] theorem join_pfilter {o : Option (Option α)} {p : (o' : Option α) → o = some o' → Bool} :
    (o.pfilter p).join = o.pbind (fun o' ho' => if p o' ho' then o' else none) := by
  cases o <;> simp <;> split <;> simp

@[grind =] theorem elim_pfilter {o : Option α} {b : β} {f : α → β} {p : (a : α) → o = some a → Bool} :
    (o.pfilter p).elim b f = o.pelim b (fun a ha => if p a ha then f a else b) := by
  cases o with
  | none => simp
  | some a =>
    simp only [pfilter_some, pelim_some]
    split <;> simp

@[grind =] theorem pelim_pfilter {o : Option α} {b : β} {p : (a : α) → o = some a → Bool}
    {f : (a : α) → o.pfilter p = some a → β} :
    (o.pfilter p).pelim b f = o.pelim b
      (fun a ha => if hp : p a ha then f a (pfilter_eq_some_iff.2 ⟨_, hp⟩) else b) := by
  cases o with
  | none => simp
  | some a =>
    simp only [pfilter_some, pelim_some]
    split <;> simp

theorem pfilter_guard {a : α} {p : α → Bool} {q : (a' : α) → guard p a = some a' → Bool} :
    (guard p a).pfilter q = if ∃ (h : p a), q a (by simp [h]) then some a else none := by
  simp only [guard]
  split <;> simp_all

/-! ### LT and LE -/

@[simp] theorem not_lt_none [LT α] {a : Option α} : ¬ a < none := by cases a <;> simp [LT.lt, Option.lt]
theorem none_lt_some [LT α] {a : α} : none < some a := by simp [LT.lt, Option.lt]
@[simp] theorem none_lt [LT α] {a : Option α} : none < a ↔ a.isSome := by cases a <;> simp [none_lt_some]
@[simp] theorem some_lt_some [LT α] {a b : α} : some a < some b ↔ a < b := by simp [LT.lt, Option.lt]

@[simp] theorem none_le [LE α] {a : Option α} : none ≤ a := by cases a <;> simp [LE.le, Option.le]
theorem not_some_le_none [LE α] {a : α} : ¬ some a ≤ none := by simp [LE.le, Option.le]
@[simp] theorem le_none [LE α] {a : Option α} : a ≤ none ↔ a = none := by cases a <;> simp [not_some_le_none]
@[simp] theorem some_le_some [LE α] {a b : α} : some a ≤ some b ↔ a ≤ b := by simp [LE.le, Option.le]

grind_pattern not_lt_none => a < none
grind_pattern none_lt_some => none < some a
grind_pattern some_lt_some => some a < some b
grind_pattern none_le => none ≤ a
grind_pattern not_some_le_none => some a ≤ none
grind_pattern some_le_some => some a ≤ some b

@[simp]
theorem filter_le [LE α] (le_refl : ∀ x : α, x ≤ x) {o : Option α} {p : α → Bool} : o.filter p ≤ o := by
  cases o with
  | none => simp
  | some _ =>
    simp only [filter_some]
    split <;> simp [le_refl]

@[simp]
theorem filter_lt [LT α] (lt_irrefl : ∀ x : α, ¬x < x) {o : Option α} {p : α → Bool} : o.filter p < o ↔ o.any (fun a => !p a) := by
  cases o with
  | none => simp
  | some _ =>
    simp only [filter_some]
    split <;> simp [*]

@[simp]
theorem le_filter [LE α] (le_refl : ∀ x : α, x ≤ x) {o : Option α} {p : α → Bool} : o ≤ o.filter p ↔ o.all p := by
  cases o with
  | none => simp
  | some _ =>
    simp only [filter_some]
    split <;> simp [*]

@[simp]
theorem not_lt_filter [LT α] (lt_irrefl : ∀ x : α, ¬x < x) {o : Option α} {p : α → Bool} : ¬o < o.filter p := by
  cases o with
  | none => simp
  | some _ =>
    simp only [filter_some]
    split <;> simp [lt_irrefl]

@[simp]
theorem pfilter_le [LE α] (le_refl : ∀ x : α, x ≤ x) {o : Option α} {p : (a : α) → o = some a → Bool} :
    o.pfilter p ≤ o := by
  cases o with
  | none => simp
  | some _ =>
    simp only [pfilter_some]
    split <;> simp [*]

@[simp]
theorem not_lt_pfilter [LT α] (lt_irrefl : ∀ x : α, ¬x < x) {o : Option α}
    {p : (a : α) → o = some a → Bool} : ¬o < o.pfilter p := by
  cases o with
  | none => simp
  | some _ =>
    simp only [pfilter_some]
    split <;> simp [lt_irrefl]

theorem join_le [LE α] {o : Option (Option α)} {o' : Option α} : o.join ≤ o' ↔ o ≤ some o' := by
  cases o <;> simp

@[simp]
theorem guard_le_some [LE α] (le_refl : ∀ x : α, x ≤ x) {x : α} {p : α → Bool} : guard p x ≤ some x := by
  simp only [guard_eq_ite]
  split <;> simp [le_refl]

@[simp]
theorem guard_lt_some [LT α] (lt_irrefl : ∀ x : α, ¬x < x) {x : α} {p : α → Bool} :
    guard p x < some x ↔ p x = false := by
  simp only [guard_eq_ite]
  split <;> simp [*]

theorem left_le_of_merge_le [LE α] {f : α → α → α} (hf : ∀ a b c, f a b ≤ c → a ≤ c)
    {o₁ o₂ o₃ : Option α} : o₁.merge f o₂ ≤ o₃ → o₁ ≤ o₃ := by
  cases o₁ <;> cases o₂ <;> cases o₃ <;> try (simp; done)
  simpa using hf _ _ _

theorem right_le_of_merge_le [LE α] {f : α → α → α} (hf : ∀ a b c, f a b ≤ c → b ≤ c)
    {o₁ o₂ o₃ : Option α} : o₁.merge f o₂ ≤ o₃ → o₂ ≤ o₃ := by
  cases o₁ <;> cases o₂ <;> cases o₃ <;> try (simp; done)
  simpa using hf _ _ _

theorem merge_le [LE α] {f : α → α → α} {o₁ o₂ o₃ : Option α}
    (hf : ∀ a b c, a ≤ c → b ≤ c → f a b ≤ c) : o₁ ≤ o₃ → o₂ ≤ o₃ → o₁.merge f o₂ ≤ o₃ := by
  cases o₁ <;> cases o₂ <;> cases o₃ <;> try (simp; done)
  simpa using hf _ _ _

@[simp]
theorem merge_le_iff [LE α] {f : α → α → α} {o₁ o₂ o₃ : Option α}
    (hf : ∀ a b c, f a b ≤ c ↔ a ≤ c ∧ b ≤ c) :
    o₁.merge f o₂ ≤ o₃ ↔ o₁ ≤ o₃ ∧ o₂ ≤ o₃ := by
  cases o₁ <;> cases o₂ <;> cases o₃ <;> simp [*]

theorem left_lt_of_merge_lt [LT α] {f : α → α → α} (hf : ∀ a b c, f a b < c → a < c)
    {o₁ o₂ o₃ : Option α} : o₁.merge f o₂ < o₃ → o₁ < o₃ := by
  cases o₁ <;> cases o₂ <;> cases o₃ <;> try (simp; done)
  simpa using hf _ _ _

theorem right_lt_of_merge_lt [LT α] {f : α → α → α} (hf : ∀ a b c, f a b < c → b < c)
    {o₁ o₂ o₃ : Option α} : o₁.merge f o₂ < o₃ → o₂ < o₃ := by
  cases o₁ <;> cases o₂ <;> cases o₃ <;> try (simp; done)
  simpa using hf _ _ _

theorem merge_lt [LT α] {f : α → α → α} {o₁ o₂ o₃ : Option α}
    (hf : ∀ a b c, a < c → b < c → f a b < c) : o₁ < o₃ → o₂ < o₃ → o₁.merge f o₂ < o₃ := by
  cases o₁ <;> cases o₂ <;> cases o₃ <;> try (simp; done)
  simpa using hf _ _ _

@[simp]
theorem merge_lt_iff [LT α] {f : α → α → α} {o₁ o₂ o₃ : Option α}
    (hf : ∀ a b c, f a b < c ↔ a < c ∧ b < c) :
    o₁.merge f o₂ < o₃ ↔ o₁ < o₃ ∧ o₂ < o₃ := by
  cases o₁ <;> cases o₂ <;> cases o₃ <;> simp [*]

/-! ### Rel -/

@[simp] theorem rel_some_some {r : α → β → Prop} : Rel r (some a) (some b) ↔ r a b :=
  ⟨fun | .some h => h, .some⟩
@[simp] theorem not_rel_some_none {r : α → β → Prop} : ¬Rel r (some a) none := nofun
@[simp] theorem not_rel_none_some {r : α → β → Prop} : ¬Rel r none (some a) := nofun
@[simp] theorem rel_none_none {r : α → β → Prop} : Rel r none none := .none

/-! ### min and max -/

theorem min_eq_left [LE α] [Min α] (min_eq_left : ∀ x y : α, x ≤ y → min x y = x)
    {a b : Option α} (h : a ≤ b) : min a b = a := by
  cases a <;> cases b <;> simp_all

theorem min_eq_right [LE α] [Min α] (min_eq_right : ∀ x y : α, y ≤ x → min x y = y)
    {a b : Option α} (h : b ≤ a) : min a b = b := by
  cases a <;> cases b <;> simp_all

theorem min_eq_left_of_lt [LT α] [Min α] (min_eq_left : ∀ x y : α, x < y → min x y = x)
    {a b : Option α} (h : a < b) : min a b = a := by
  cases a <;> cases b <;> simp_all

theorem min_eq_right_of_lt [LT α] [Min α] (min_eq_right : ∀ x y : α, y < x → min x y = y)
    {a b : Option α} (h : b < a) : min a b = b := by
  cases a <;> cases b <;> simp_all

theorem min_eq_or [LE α] [Min α] (min_eq_or : ∀ x y : α, min x y = x ∨ min x y = y)
    {a b : Option α} : min a b = a ∨ min a b = b := by
  cases a <;> cases b <;> simp_all

theorem min_le_left [LE α] [Min α] (min_le_left : ∀ x y : α, min x y ≤ x)
    {a b : Option α} : min a b ≤ a := by
  cases a <;> cases b <;> simp_all

theorem min_le_right [LE α] [Min α] (min_le_right : ∀ x y : α, min x y ≤ y)
    {a b : Option α} : min a b ≤ b := by
  cases a <;> cases b <;> simp_all

theorem le_min [LE α] [Min α] (le_min : ∀ x y z : α, x ≤ min y z ↔ x ≤ y ∧ x ≤ z)
    {a b c : Option α} : a ≤ min b c ↔ a ≤ b ∧ a ≤ c := by
  cases a <;> cases b <;> cases c <;> simp_all

theorem max_eq_left [LE α] [Max α] (max_eq_left : ∀ x y : α, x ≤ y → max x y = y)
    {a b : Option α} (h : a ≤ b) : max a b = b := by
  cases a <;> cases b <;> simp_all

theorem max_eq_right [LE α] [Max α] (max_eq_right : ∀ x y : α, y ≤ x → max x y = x)
    {a b : Option α} (h : b ≤ a) : max a b = a := by
  cases a <;> cases b <;> simp_all

theorem max_eq_left_of_lt [LT α] [Max α] (max_eq_left : ∀ x y : α, x < y → max x y = y)
    {a b : Option α} (h : a < b) : max a b = b := by
  cases a <;> cases b <;> simp_all

theorem max_eq_right_of_lt [LT α] [Max α] (max_eq_right : ∀ x y : α, y < x → max x y = x)
    {a b : Option α} (h : b < a) : max a b = a := by
  cases a <;> cases b <;> simp_all

theorem max_eq_or [LE α] [Max α] (max_eq_or : ∀ x y : α, max x y = x ∨ max x y = y)
    {a b : Option α} : max a b = a ∨ max a b = b := by
  cases a <;> cases b <;> simp_all

theorem left_le_max [LE α] [Max α] (le_refl : ∀ x : α, x ≤ x) (left_le_max : ∀ x y : α, x ≤ max x y)
    {a b : Option α} : a ≤ max a b := by
  cases a <;> cases b <;> simp_all

theorem right_le_max [LE α] [Max α] (le_refl : ∀ x : α, x ≤ x) (right_le_max : ∀ x y : α, y ≤ max x y)
    {a b : Option α} : b ≤ max a b := by
  cases a <;> cases b <;> simp_all

theorem max_le [LE α] [Max α] (max_le : ∀ x y z : α, max x y ≤ z ↔ x ≤ z ∧ y ≤ z)
    {a b c : Option α} : max a b ≤ c ↔ a ≤ c ∧ b ≤ c := by
  cases a <;> cases b <;> cases c <;> simp_all

@[simp]
theorem merge_max [Max α] : merge (α := α) max = max := by
  funext a b; cases a <;> cases b <;> rfl

instance [Max α] : Std.LawfulIdentity (α := Option α) max none := by
  rw [← merge_max]; infer_instance

instance [Max α] [Std.IdempotentOp (α := α) max] : Std.IdempotentOp (α := Option α) max where
  idempotent o := by cases o <;> simp [Std.IdempotentOp.idempotent]

@[simp]
theorem max_filter_left [Max α] [Std.IdempotentOp (α := α) max] {p : α → Bool} {o : Option α} :
    max (o.filter p) o = o := by
  cases o with
  | none => simp
  | some _ =>
    simp only [filter_some]
    split <;> simp [Std.IdempotentOp.idempotent]

@[simp]
theorem max_filter_right [Max α] [Std.IdempotentOp (α := α) max] {p : α → Bool} {o : Option α} :
    max o (o.filter p) = o := by
  cases o with
  | none => simp
  | some _ =>
    simp only [filter_some]
    split <;> simp [Std.IdempotentOp.idempotent]

@[simp]
theorem min_filter_left [Min α] [Std.IdempotentOp (α := α) min] {p : α → Bool} {o : Option α} :
    min (o.filter p) o = o.filter p := by
  cases o with
  | none => simp
  | some _ =>
    simp only [filter_some]
    split <;> simp [Std.IdempotentOp.idempotent]

@[simp]
theorem min_filter_right [Min α] [Std.IdempotentOp (α := α) min] {p : α → Bool} {o : Option α} :
    min o (o.filter p) = o.filter p := by
  cases o with
  | none => simp
  | some _ =>
    simp only [filter_some]
    split <;> simp [Std.IdempotentOp.idempotent]

@[simp]
theorem max_pfilter_left [Max α] [Std.IdempotentOp (α := α) max] {o : Option α} {p : (a : α) → o = some a → Bool} :
    max (o.pfilter p) o = o := by
  cases o with
  | none => simp
  | some _ =>
    simp only [pfilter_some]
    split <;> simp [Std.IdempotentOp.idempotent]

@[simp]
theorem max_pfilter_right [Max α] [Std.IdempotentOp (α := α) max] {o : Option α} {p : (a : α) → o = some a → Bool} :
    max o (o.pfilter p) = o := by
  cases o with
  | none => simp
  | some _ =>
    simp only [pfilter_some]
    split <;> simp [Std.IdempotentOp.idempotent]

@[simp]
theorem min_pfilter_left [Min α] [Std.IdempotentOp (α := α) min] {o : Option α} {p : (a : α) → o = some a → Bool} :
    min (o.pfilter p) o = o.pfilter p := by
  cases o with
  | none => simp
  | some _ =>
    simp only [pfilter_some]
    split <;> simp [Std.IdempotentOp.idempotent]

@[simp]
theorem min_pfilter_right [Min α] [Std.IdempotentOp (α := α) min] {o : Option α} {p : (a : α) → o = some a → Bool} :
    min o (o.pfilter p) = o.pfilter p := by
  cases o with
  | none => simp
  | some _ =>
    simp only [pfilter_some]
    split <;> simp [Std.IdempotentOp.idempotent]

@[simp, grind =]
theorem isSome_max [Max α] {o o' : Option α} : (max o o').isSome = (o.isSome || o'.isSome) := by
  cases o <;> cases o' <;> simp

@[simp, grind =]
theorem isNone_max [Max α] {o o' : Option α} : (max o o').isNone = (o.isNone && o'.isNone) := by
  cases o <;> cases o' <;> simp

@[simp, grind =]
theorem isSome_min [Min α] {o o' : Option α} : (min o o').isSome = (o.isSome && o'.isSome) := by
  cases o <;> cases o' <;> simp

@[simp, grind =]
theorem isNone_min [Min α] {o o' : Option α} : (min o o').isNone = (o.isNone || o'.isNone) := by
  cases o <;> cases o' <;> simp

theorem max_join_left [Max α] {o : Option (Option α)} {o' : Option α} :
    max o.join o' = (max o (some o')).get (by simp) := by
  cases o <;> simp

theorem max_join_right [Max α] {o : Option α} {o' : Option (Option α)} :
    max o o'.join = (max (some o) o').get (by simp) := by
  cases o' <;> simp

@[grind _=_] theorem join_max [Max α] {o o' : Option (Option α)} :
    (max o o').join = max o.join o'.join := by
  cases o <;> cases o' <;> simp

theorem min_join_left [Min α] {o : Option (Option α)} {o' : Option α} :
    min o.join o' = (min o (some o')).join := by
  cases o <;> simp

theorem min_join_right [Min α] {o : Option α} {o' : Option (Option α)} :
    min o o'.join = (min (some o) o').join := by
  cases o' <;> simp

@[grind _=_] theorem join_min [Min α] {o o' : Option (Option α)} :
    (min o o').join = min o.join o'.join := by
  cases o <;> cases o' <;> simp

@[simp]
theorem min_guard_some [Min α] [Std.IdempotentOp (α := α) min] {x : α} {p : α → Bool} :
    min (guard p x) (some x) = guard p x := by
  simp only [guard_eq_ite]
  split <;> simp [Std.IdempotentOp.idempotent]

@[simp]
theorem min_some_guard [Min α] [Std.IdempotentOp (α := α) min] {x : α} {p : α → Bool} :
    min (some x) (guard p x) = guard p x := by
  simp only [guard_eq_ite]
  split <;> simp [Std.IdempotentOp.idempotent]

@[simp]
theorem max_guard_some [Max α] [Std.IdempotentOp (α := α) max] {x : α} {p : α → Bool} :
    max (guard p x) (some x) = some x := by
  simp only [guard_eq_ite]
  split <;> simp [Std.IdempotentOp.idempotent]

@[simp]
theorem max_some_guard [Max α] [Std.IdempotentOp (α := α) max] {x : α} {p : α → Bool} :
    max (some x) (guard p x) = some x := by
  simp only [guard_eq_ite]
  split <;> simp [Std.IdempotentOp.idempotent]

theorem max_eq_some_iff [Max α] {o o' : Option α} {a : α} :
    max o o' = some a ↔ (o = some a ∧ o' = none) ∨ (o = none ∧ o' = some a) ∨
      (∃ b c, o = some b ∧ o' = some c ∧ max b c = a) := by
  cases o <;> cases o' <;> simp

@[simp]
theorem max_eq_none_iff [Max α] {o o' : Option α} :
    max o o' = none ↔ o = none ∧ o' = none := by
  cases o <;> cases o' <;> simp

@[simp]
theorem min_eq_some_iff [Min α] {o o' : Option α} {a : α} :
    min o o' = some a ↔ ∃ b c, o = some b ∧ o' = some c ∧ min b c = a := by
  cases o <;> cases o' <;> simp

@[simp]
theorem min_eq_none_iff [Min α] {o o' : Option α} :
    min o o' = none ↔ o = none ∨ o' = none := by
  cases o <;> cases o' <;> simp

@[simp, grind =]
theorem any_max [Max α] {o o' : Option α} {p : α → Bool} (hp : ∀ a b, p (max a b) = (p a || p b)) :
    (max o o').any p = (o.any p || o'.any p) := by
  cases o <;> cases o' <;> simp [hp]

@[simp, grind =]
theorem all_min [Min α] {o o' : Option α} {p : α → Bool} (hp : ∀ a b, p (min a b) = (p a || p b)) :
    (min o o').all p = (o.all p || o'.all p) := by
  cases o <;> cases o' <;> simp [hp]

theorem isSome_left_of_isSome_min [Min α] {o o' : Option α} : (min o o').isSome → o.isSome := by
  cases o <;> simp

theorem isSome_right_of_isSome_min [Min α] {o o' : Option α} : (min o o').isSome → o'.isSome := by
  cases o' <;> simp

@[simp, grind =]
theorem get_min [Min α] {o o' : Option α} {h} :
    (min o o').get h = min (o.get (isSome_left_of_isSome_min h)) (o'.get (isSome_right_of_isSome_min h)) := by
  cases o <;> cases o' <;> simp

theorem map_max [Max α] [Max β] {o o' : Option α} {f : α → β} (hf : ∀ x y, f (max x y) = max (f x) (f y)) :
    (max o o').map f = max (o.map f) (o'.map f) := by
  cases o <;> cases o' <;> simp [*]

theorem map_min [Min α] [Min β] {o o' : Option α} {f : α → β} (hf : ∀ x y, f (min x y) = min (f x) (f y)) :
    (min o o').map f = min (o.map f) (o'.map f) := by
  cases o <;> cases o' <;> simp [*]

theorem wellFounded_lt {α} {rel : α → α → Prop} (h : WellFounded rel) :
    WellFounded (Option.lt rel) := by
  refine ⟨fun x => ?_⟩
  have hn : Acc (Option.lt rel) none := by
    refine Acc.intro none ?_
    intro y hyx
    cases y <;> cases hyx
  cases x
  · exact hn
  · rename_i x
    induction h.apply x
    rename_i _ _ ih
    refine Acc.intro _ (fun y hy => ?_)
    cases y
    · exact hn
    · exact ih _ hy

theorem SomeLtNone.wellFounded_lt {α} {r : α → α → Prop} (h : WellFounded r) :
    WellFounded (SomeLtNone.lt r) := by
  refine ⟨?_⟩
  intro x
  constructor
  intro x' hlt
  match x' with
  | none => contradiction
  | some x' =>
    clear hlt
    induction h.apply x'
    rename_i ih
    refine Acc.intro _ (fun x'' hlt' => ?_)
    match x'' with
    | none => contradiction
    | some x'' => exact ih x'' hlt'

end Option

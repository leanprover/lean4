/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
prelude
import Init.Data.Option.Instances
import Init.Classical
import Init.Ext

namespace Option

theorem mem_iff {a : α} {b : Option α} : a ∈ b ↔ b = a := .rfl

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

@[simp] theorem some_get : ∀ {x : Option α} (h : isSome x), some (x.get h) = x
| some _, _ => rfl

@[simp] theorem get_some (x : α) (h : isSome (some x)) : (some x).get h = x := rfl

theorem getD_of_ne_none {x : Option α} (hx : x ≠ none) (y : α) : some (x.getD y) = x := by
  cases x; {contradiction}; rw [getD_some]

theorem getD_eq_iff {o : Option α} {a b} : o.getD a = b ↔ (o = some b ∨ o = none ∧ a = b) := by
  cases o <;> simp

theorem mem_unique {o : Option α} {a b : α} (ha : a ∈ o) (hb : b ∈ o) : a = b :=
  some.inj <| ha ▸ hb

@[ext] theorem ext : ∀ {o₁ o₂ : Option α}, (∀ a, a ∈ o₁ ↔ a ∈ o₂) → o₁ = o₂
  | none, none, _ => rfl
  | some _, _, H => ((H _).1 rfl).symm
  | _, some _, H => (H _).2 rfl

theorem eq_none_iff_forall_not_mem : o = none ↔ ∀ a, a ∉ o :=
  ⟨fun e a h => by rw [e] at h; (cases h), fun h => ext <| by simp; exact h⟩

@[simp] theorem isSome_none : @isSome α none = false := rfl

@[simp] theorem isSome_some : isSome (some a) = true := rfl

theorem isSome_iff_exists : isSome x ↔ ∃ a, x = some a := by cases x <;> simp [isSome]

@[simp] theorem isNone_none : @isNone α none = true := rfl

@[simp] theorem isNone_some : isNone (some a) = false := rfl

@[simp] theorem not_isSome : isSome a = false ↔ a.isNone = true := by
  cases a <;> simp

theorem eq_some_iff_get_eq : o = some a ↔ ∃ h : o.isSome, o.get h = a := by
  cases o <;> simp; nofun

theorem eq_some_of_isSome : ∀ {o : Option α} (h : o.isSome), o = some (o.get h)
  | some _, _ => rfl

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
  cases x <;> simp only [map_none', map_some', eq_self_iff_true]

theorem map_eq_none : f <$> x = none ↔ x = none := map_eq_none'

theorem map_eq_bind {x : Option α} : x.map f = x.bind (some ∘ f) := by
  cases x <;> simp [Option.bind]

theorem map_congr {x : Option α} (h : ∀ a, a ∈ x → f a = g a) : x.map f = x.map g := by
  cases x <;> simp only [map_none', map_some', h, mem_def]

@[simp] theorem map_id' : Option.map (@id α) = id := map_id
@[simp] theorem map_id'' {x : Option α} : (x.map fun a => a) = x := congrFun map_id x

@[simp] theorem map_map (h : β → γ) (g : α → β) (x : Option α) :
    (x.map g).map h = x.map (h ∘ g) := by
  cases x <;> simp only [map_none', map_some', ·∘·]

theorem comp_map (h : β → γ) (g : α → β) (x : Option α) : x.map (h ∘ g) = (x.map g).map h :=
  (map_map ..).symm

@[simp] theorem map_comp_map (f : α → β) (g : β → γ) :
    Option.map g ∘ Option.map f = Option.map (g ∘ f) := by funext x; simp

theorem mem_map_of_mem (g : α → β) (h : a ∈ x) : g a ∈ Option.map g x := h.symm ▸ map_some' ..

theorem bind_map_comm {α β} {x : Option (Option α)} {f : α → β} :
    x.bind (Option.map f) = (x.map (Option.map f)).bind id := by cases x <;> simp

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

theorem liftOrGet_eq_or_eq {f : α → α → α} (h : ∀ a b, f a b = a ∨ f a b = b) :
    ∀ o₁ o₂, liftOrGet f o₁ o₂ = o₁ ∨ liftOrGet f o₁ o₂ = o₂
  | none, none => .inl rfl
  | some a, none => .inl rfl
  | none, some b => .inr rfl
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

section

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

end

@[simp] theorem toList_some (a : α) : (a : Option α).toList = [a] := rfl

@[simp] theorem toList_none (α : Type _) : (none : Option α).toList = [] := rfl

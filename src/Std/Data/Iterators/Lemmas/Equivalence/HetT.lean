/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
prelude
import Init.Control.Lawful.Basic
import Init.Data.Subtype
import Init.PropLemmas
import Init.Classical
import Init.Data.Iterators.Internal.LawfulMonadLiftFunction
import Init.Data.Iterators.PostconditionMonad

namespace Std.Internal

section Small

universe u v

class ComputableSmall (α : Type v) where
  Target : Type u
  deflate : α → Target
  inflate : Target → α
  deflate_inflate : ∀ {a}, deflate (inflate a) = a
  inflate_deflate : ∀ {a}, inflate (deflate a) = a

class Small (α : Type v) : Prop where
  h : Nonempty (ComputableSmall.{u} α)

noncomputable def ComputableSmall.choose (α : Type v) [small : Small.{u} α] : ComputableSmall.{u} α :=
  haveI : Nonempty (ComputableSmall.{u} α) := Small.h
  Classical.ofNonempty (α := ComputableSmall.{u} α)

variable {α : Type v} {β : Type u}

structure USquash (α : Type v) [small : Small.{u} α] where
  mk' ::
  inner : (ComputableSmall.choose α).Target

def USquashOrUnit (α : Type v) := open Classical in if _ : Small.{u} α then USquash.{u} α else PUnit

theorem uSquash_eq_uSquashOrUnit {α : Type v} [Small.{u} α] : USquash.{u} α = USquashOrUnit.{u} α := by
  rw [USquashOrUnit, dif_pos]

noncomputable def USquash.deflate [small : Small.{u} α] (x : α) : USquash.{u} α := USquash.mk' (ComputableSmall.choose α |>.deflate x)

noncomputable def USquash.inflate [small : Small.{u} α] (x : USquash.{u} α) : α := ComputableSmall.choose α |>.inflate x.inner

@[simp]
theorem USquash.deflate_inflate {_ : Small.{u} α} {x : USquash.{u} α} :
    USquash.deflate x.inflate = x := by
  simp [deflate, inflate, ComputableSmall.deflate_inflate]

@[simp]
theorem USquash.inflate_deflate {_ : Small.{u} α} {x : α} :
    (USquash.deflate.{u} x).inflate = x := by
  simp [deflate, inflate, ComputableSmall.inflate_deflate]

theorem USquash.inflate.inj {_ : Small.{u} α} {x y : USquash α} (h : x.inflate = y.inflate) : x = y := by
  rw [← deflate_inflate (x := x), ← deflate_inflate (x := y), h]

instance {α : Type v} : Small.{v} α := ⟨⟨{
    Target := α
    deflate := id
    inflate := id
    deflate_inflate := rfl
    inflate_deflate := rfl }⟩⟩

instance {α : Type v} [Small.{u} α] {p : α → Prop} : Small.{u} (Subtype p) where
  h := ⟨{
    Target := Subtype (p ∘ USquash.inflate : USquash.{u} α → Prop)
    deflate x := ⟨USquash.deflate x.1, by simp [x.2]⟩
    inflate x := ⟨USquash.inflate x.1, x.2⟩
    deflate_inflate := by simp
    inflate_deflate := by simp }⟩

instance {α : Type v} {x : α} : Small.{u} (Subtype (x = ·)) where
  h := ⟨{
    Target := PUnit
    deflate _ := .unit
    inflate _ := ⟨x, rfl⟩
    deflate_inflate := rfl
    inflate_deflate := by rintro ⟨_, rfl⟩; rfl
  }⟩

instance {α : Type v} {x : α} : Small.{u} (Subtype (· = x)) where
  h := ⟨{
    Target := PUnit
    deflate _ := .unit
    inflate _ := ⟨x, rfl⟩
    deflate_inflate := rfl
    inflate_deflate := by rintro ⟨_, rfl⟩; rfl
  }⟩

def Small.of_surjective (α : Type v) {β : Type w} (f : α → β) [Small.{u} α]
    (h : ∀ b, ∃ a, f a = b) : Small.{u} β where
  h := ⟨{
    Target := Quot (fun a a' : USquash α => f a.inflate = f a'.inflate)
    deflate b := Quot.mk _ (.deflate (h b).choose)
    inflate := Quot.lift (f ·.inflate) (fun a a' => id)
    deflate_inflate {x} := by
      rcases x.exists_rep with ⟨x, rfl⟩
      apply Quot.sound
      simp [(h (f x.inflate)).choose_spec]
    inflate_deflate {b} := by simp [(h b).choose_spec]
  }⟩

instance {α : Type v} {β : Type w} {f : α → β} [Small.{u} α] :
    Small.{u} { b : β // ∃ a, f a = b } := .of_surjective α (fun a => ⟨f a, a, rfl⟩)
        (fun b => ⟨b.2.choose, by simp; ext; exact b.2.choose_spec⟩)

theorem Small.map {α : Type v} {β : Type w} (P : α → Prop) (f : (a : α) → P a → β)
    [Small.{u} { a // P a }] :
    Small.{u} { b // ∃ a h, f a h = b } := .of_surjective { a // P a }
        (fun x => ⟨f x.1 x.2, x.1, x.2, rfl⟩)
        (fun y => ⟨⟨y.2.choose, y.2.choose_spec.choose⟩, (by
            simp only
            ext
            exact y.2.choose_spec.choose_spec)⟩)

instance {α : Type v} {β : α → Type w} [Small.{u} α] [∀ a, Small.{u} (β a)] :
    Small.{u} ((a : α) × β a) := .of_surjective
        ((a : USquash α) × (USquash (β a.inflate)))
        (fun x => ⟨x.1.inflate, x.2.inflate⟩)
        (fun b => ⟨⟨.deflate b.1, .deflate (USquash.inflate_deflate ▸ b.2)⟩,
          (by rcases b with ⟨b₁, b₂⟩; simp [eqRec_heq])⟩)

theorem Small.pbind {α : Type v} {β : Type w} (P : α → Prop) (Q : (a : α) → P a → β → Prop)
    (i₁ : Small.{u} { a // P a }) (i₂ : ∀ a h, Small.{u} { b // Q a h b }) :
    Small.{u} { b // ∃ a h, Q a h b } := .of_surjective
        ((a : { a // P a }) × { b // Q a.1 a.2 b })
        (fun x => ⟨x.2.1, x.1, x.1.2, x.2.2⟩)
        (fun y => ⟨⟨⟨y.2.choose, y.2.choose_spec.1⟩, y.1, y.2.choose_spec.2⟩, rfl⟩)

theorem Small.bind {α : Type v} {β : Type w} (P : α → Prop) (Q : α → β → Prop)
    (i₁ : Small.{u} { a // P a }) (i₂ : ∀ a, Small.{u} { b // Q a b }) :
    Small.{u} { b // ∃ a, P a ∧ Q a b } := .of_surjective
        ((a : { a // P a }) × { b // Q a b })
        (fun x => ⟨x.2.1, x.1, x.1.2, x.2.2⟩)
        (fun y => ⟨⟨⟨y.2.choose, y.2.choose_spec.1⟩, y.1, y.2.choose_spec.2⟩, rfl⟩)

end Small

end Std.Internal

namespace Std.Iterators
open Std.Internal

/--
If `m` is a monad, then `HetT m` is a monad that has two features:

* It generalizes `m` to arbitrary universes.
* It tracks a postcondition property that holds for the monadic return value, similarly to
  `PostconditionT`.

This monad is noncomputable and is merely a vehicle for more convenient proofs, especially proofs
about the equivalence of iterators, because it avoids universe issues and spares users the work
to handle the postconditions manually.

Caution: Just like `PostconditionT`, this is not a lawful monad transformer.
To lift from `m` to `HetT m`, use `HetT.lift`.

Because this monad is fundamentally universe-polymorphic, it is recommended for consistency to
always use the methods `HetT.pure`, `HetT.map` and `HetT.bind` instead of the homogeneous versions
`Pure.pure`, `Functor.map` and `Bind.bind`.
-/
structure HetT (m : Type w → Type w') (α : Type v) where
  /--
  A predicate that holds for the return value(s) of the `m`-monadic operation.
  -/
  Property : α → Prop
  /--
  A proof that the possible return values are equivalent to a `w`-small type.
  -/
  small : Small.{w} (Subtype Property)
  /--
  The actual monadic operation. Its return value is bundled together with a proof that
  it satisfies `Property` and squashed so that it fits into the monad `m`.
  -/
  operation : m (USquash (Subtype Property))

-- `injEq` is the shortest path to DTT hell. We use `ext_iff` instead (see below).
attribute [-simp] HetT.mk.injEq

/--
Converts `PostconditionT m α` to `HetT m α`, preserving the postcondition property.
-/
noncomputable def HetT.ofPostconditionT [Monad m] (x : PostconditionT m α) : HetT m α :=
  ⟨x.Property, inferInstance, USquash.deflate <$> x.operation⟩

noncomputable instance (m : Type w → Type w') [Monad m] : MonadLift m (HetT m) where
  monadLift x := ⟨fun _ => True, inferInstance, (USquash.deflate ⟨·, .intro⟩) <$> x⟩

/--
Lifts `x : m α` into `HetT m α` with the trivial postcondition.

Caution: This is not a lawful monad lifting function
-/
noncomputable def HetT.lift {α : Type w} {m : Type w → Type w'} [Monad m] (x : m α) :
    HetT m α :=
  x

/--
A universe-heterogeneous version of `Pure.pure`. Given `a : α`, it returns an element of `HetT m α`
with the postcondition `(a = ·)`.
-/
protected noncomputable def HetT.pure {m : Type w → Type w'} [Pure m] {α : Type v}
    (a : α) : HetT m α :=
  ⟨(a = ·), inferInstance, pure (.deflate ⟨a, rfl⟩)⟩

/--
A generalization of `HetT.map` that provides the postcondition property to the mapping function.
-/
protected noncomputable def HetT.pmap {m : Type w → Type w'} [Functor m] {α : Type u} {β : Type v}
    (x : HetT m α) (f : (a : α) → x.Property a → β) : HetT m β :=
  have : Small.{w} (Subtype x.Property) := x.small
  have := Small.map x.Property f
  ⟨fun b => ∃ a h, f a h = b, inferInstance, (fun a => .deflate ⟨f a.inflate.1 a.inflate.2, a.inflate.1, by simp [a.inflate.property]⟩) <$> x.operation⟩

/--
A universe-heterogeneous version of `Functor.map`.
-/
protected noncomputable def HetT.map {m : Type w → Type w'} [Functor m] {α : Type u} {β : Type v}
    (f : α → β) (x : HetT m α) : HetT m β :=
  x.pmap (fun a _ => f a)

/--
A generalization of `HetT.bind` that provides the postcondition property to the mapping function.
-/
protected noncomputable def HetT.pbind {m : Type w → Type w'} [Monad m] {α : Type u} {β : Type v}
    (x : HetT m α) (f : (a : α) → x.Property a → HetT m β) : HetT m β :=
  have := x.small
  have := fun a h => (f a h).small
  have := Small.pbind x.Property (fun a h b => (f a h).Property b) inferInstance inferInstance
  ⟨fun b => ∃ a h, (f a h).Property b,
    inferInstance,
    x.operation >>= fun a => ((fun b => .deflate ⟨b.inflate.1, a.inflate.1, a.inflate.2, b.inflate.2⟩) <$> (f a.inflate.1 a.inflate.2).operation)⟩

/--
A universe-heterogeneous version of `Bind.bind`.
-/
protected noncomputable def HetT.bind {m : Type w → Type w'} [Monad m] {α : Type u} {β : Type v}
    (x : HetT m α) (f : α → HetT m β) : HetT m β :=
  have := x.small
  have := fun a => (f a).small
  have := Small.bind x.Property (fun a b => (f a).Property b) inferInstance inferInstance
  ⟨fun b => ∃ a, x.Property a ∧ (f a).Property b,
    inferInstance,
    x.operation >>= fun a => ((fun b => .deflate ⟨b.inflate.1, a.inflate.1, a.inflate.2, b.inflate.2⟩) <$> (f a.inflate).operation)⟩

noncomputable instance {m : Type w → Type w'} [Functor m] : Functor (HetT m) where
  map := HetT.map

noncomputable instance {m : Type w → Type w'} [Monad m] : Monad (HetT m) where
  pure := HetT.pure
  bind := HetT.bind

/--
Applies the given function to the result of the contained `m`-monadic operation with a
proof that the postcondition property holds, returning another operation in `m`.
-/
noncomputable def HetT.prun [Monad m] (x : HetT m α) (f : (a : α) → x.Property a → m β) :
    m β :=
  x.operation >>= (fun a => letI a' := a.inflate (small := HetT.small _); f a'.1 a'.2)

@[simp]
theorem HetT.property_lift {m : Type w → Type w'} [Monad m] {x : m α} :
    (HetT.lift x).Property = (fun _ => True) :=
  rfl

@[simp]
theorem HetT.prun_lift {m : Type w → Type w'} [Monad m] [LawfulMonad m] {x : m α}
    {f : (a : α) → _ → m γ} :
    (HetT.lift x).prun f = x >>= (fun a => f a .intro) := by
  simp [HetT.prun, HetT.lift, liftM, monadLift, MonadLift.monadLift, bind_map_left]

@[simp]
theorem HetT.property_ofPostconditionT [Monad m] {x : PostconditionT m α} :
    (HetT.ofPostconditionT x).Property = x.Property :=
  rfl

@[simp]
theorem HetT.prun_ofPostconditionT [Monad m] [LawfulMonad m] {x : PostconditionT m α}
    {f : (_ : _) → _ → m γ} :
    (HetT.ofPostconditionT x).prun f = x.operation >>= (fun a => f a.1 a.2) := by
  simp [ofPostconditionT, prun]

/--
If the monad `m` is liftable to `n`, lifts `HetT m α` to `HetT n α`.
-/
noncomputable def HetT.liftInner {m : Type w → Type w'} (n : Type w → Type w'') [MonadLiftT m n]
    (x : HetT m α) : HetT n α :=
  ⟨x.Property, x.small, x.operation⟩

@[simp]
theorem HetT.property_liftInner {m : Type w → Type w'} {n : Type w → Type w''} [MonadLiftT m n]
    {x : HetT m α} : (x.liftInner n).Property = x.Property :=
  rfl

@[simp]
theorem HetT.prun_liftInner {m : Type w → Type w'} {n : Type w → Type w''} [Monad m] [Monad n]
    [MonadLiftT m n] [LawfulMonadLiftT m n] {x : HetT m α} {f : (a : α) → _ → m γ} :
    (x.liftInner n).prun (fun a ha => f a ha) = x.prun f := by
  simp [liftInner, prun]

theorem HetT.ext {m : Type w → Type w'} [Monad m] [LawfulMonad m]
    {α : Type v} {x y : HetT m α}
    (h : x.Property = y.Property)
    (h' : ∀ β, ∀ f : (a : α) → x.Property a → m β, x.prun f = y.prun (fun a ha => f a (h ▸ ha))) :
    x = y := by
  specialize h' (USquash { a // x.Property a } (small := HetT.small _)) (fun a ha => pure <| .deflate (small := _) <| Subtype.mk a ha)
  cases x; cases y; cases h
  simp only [prun, bind_pure_comp] at h'
  let h'' : (USquash.deflate <| USquash.inflate ·) <$> _ = (USquash.deflate <| USquash.inflate ·) <$> _ := h'
  simp only [USquash.deflate_inflate, id_map'] at h''
  simp [h'']

theorem HetT.ext_iff {m : Type w → Type w'} [Monad m] [LawfulMonad m]
    {α : Type v} {x y : HetT m α} :
    x = y ↔ ∃ h : x.Property = y.Property, ∀ β, ∀ f : (a : α) → x.Property a → m β, x.prun f = y.prun (fun a ha => f a (h ▸ ha)) := by
  constructor
  · rintro rfl
    refine ⟨rfl, ?_⟩
    intro β f
    rfl
  · intro h
    exact HetT.ext h.1 h.2

@[simp]
protected theorem HetT.map_eq_pure_bind {m : Type w → Type w'} [Monad m] [LawfulMonad m]
    {α : Type u} {β : Type v} {f : α → β} {x : HetT m α} :
    x.map f = x.bind (HetT.pure ∘ f) := by
  simp [HetT.map, HetT.pmap, HetT.bind, HetT.pure, HetT.ext_iff, prun]

@[simp]
theorem HetT.property_pure {m : Type w → Type w'} {α : Type u} [Monad m] [LawfulMonad m] {x : α} :
    (HetT.pure x : HetT m α).Property = (x = ·) := by
  simp [HetT.pure]

@[simp]
theorem HetT.prun_pure {m : Type w → Type w'} {α : Type u} {β : Type w} [Monad m]
    [LawfulMonad m] {x : α} {f : (a : α) → (HetT.pure x : HetT m α).Property a → m β} :
    (HetT.pure x).prun f = f x rfl := by
  simp [prun, HetT.pure]

@[simp]
theorem HetT.property_pbind {m : Type w → Type w'} {α : Type u} {β : Type v} [Monad m]
    [LawfulMonad m] {x : HetT m α} {f : (a : α) → x.Property a → HetT m β} :
    (x.pbind f).Property = (fun b => ∃ a h, (f a h).Property b) := by
  simp [HetT.pbind]

@[simp]
theorem HetT.prun_pbind {m : Type w → Type w'} {α : Type u} {β : Type v} {γ : Type w} [Monad m]
    [LawfulMonad m] {x : HetT m α} {f : (a : α) → x.Property a → HetT m β} {g : (b : β) → _ → m γ} :
    (x.pbind f).prun g = x.prun (fun a ha => (f a ha).prun (fun b hb => g b ⟨a, ha, hb⟩)) := by
  simp [HetT.prun, HetT.pbind]

@[simp]
theorem HetT.property_bind {m : Type w → Type w'} {α : Type u} {β : Type v} [Monad m]
    [LawfulMonad m] {x : HetT m α} {f : α → HetT m β} :
    (x.bind f).Property = (fun b => ∃ a, x.Property a ∧ (f a).Property b) := by
  simp [HetT.bind]

@[simp]
theorem HetT.prun_bind {m : Type w → Type w'} {α : Type u} {β : Type v} {γ : Type w}
    [Monad m] [LawfulMonad m] {x : HetT m α} {f : α → HetT m β} {g : (b : β) → _ → m γ} :
    (x.bind f).prun g = x.prun (fun a ha => (f a).prun (fun b hb => g b ⟨a, ha, hb⟩)) := by
  simp [HetT.prun, HetT.bind]

theorem HetT.bind_eq_pbind {m : Type w → Type w'} [Monad m] [LawfulMonad m] {α : Type u}
    {β : Type v} (x : HetT m α) (f : α → HetT m β) :
    x.bind f = x.pbind (fun a _ => f a) := by
  simp [HetT.ext_iff]

@[simp]
theorem HetT.property_pmap {m : Type w → Type w'} {α : Type u} {β : Type v} [Monad m]
    [LawfulMonad m] {x : HetT m α} {f : (a : α) → _ → β} :
    (x.pmap f).Property = (fun b => ∃ a h, f a h = b) := by
  simp [HetT.pmap]

@[simp]
theorem HetT.prun_pmap {m : Type w → Type w'} {α : Type u} {β : Type v} {γ : Type w}
    [Monad m] [LawfulMonad m] {x : HetT m α} {f : (a : α) → _ → β} {g : (b : β) → _ → m γ} :
    (x.pmap f).prun g = x.prun (fun a ha => g (f a ha) ⟨a, ha, rfl⟩) := by
  simp [HetT.prun, HetT.pmap]

@[simp]
protected theorem HetT.pure_bind {m : Type w → Type w'} [Monad m] [LawfulMonad m]
    {α : Type u} {β : Type v} {f : α → HetT m β} {a : α} :
    (HetT.pure a : HetT m α).bind f = f a := by
  simp [ext_iff]

@[simp]
protected theorem HetT.bind_pure {m : Type w → Type w'} [Monad m] [LawfulMonad m]
    {α : Type u} {x : HetT m α} :
    x.bind HetT.pure = x := by
  simp [ext_iff]

@[simp]
protected theorem HetT.bind_assoc {m : Type w → Type w'} [Monad m] [LawfulMonad m]
    {α : Type u} {β : Type v} {γ : Type x} {x : HetT m α} {f : α → HetT m β} {g : β → HetT m γ} :
    (x.bind f).bind g = x.bind (fun a => (f a).bind g) := by
  simp [ext_iff]
  ext c
  constructor
  · rintro ⟨b, ⟨a, ha, hb⟩, h⟩
    exact ⟨a, ha, b, hb, h⟩
  · rintro ⟨a, ha, b, hb, h⟩
    exact ⟨b, ⟨a, ha, hb⟩, h⟩

@[simp]
protected theorem HetT.map_pure {m : Type w → Type w'} [Monad m] [LawfulMonad m]
    {α : Type u} {β : Type v} {f : α → β} {a : α} :
    (HetT.pure a : HetT m α).map f = HetT.pure (f a) := by
  simp

@[simp]
protected theorem HetT.comp_map {m : Type w → Type w'} [Monad m] [LawfulMonad m]
    {α : Type u} {β : Type v} {γ : Type x} {f : α → β} {g : β → γ} {x : HetT m α} :
    x.map (g ∘ f) = (x.map f).map g := by
  simp [ext_iff]

@[congr]
theorem HetT.prun_congr {m : Type w → Type w'} {α : Type u} {β : Type w} [Monad m] [LawfulMonad m]
    {x y : HetT m α} {f : (a : α) → _ → m β} (h : x = y) :
    x.prun f = y.prun (fun a ha => f a (h ▸ ha)) := by
  cases h
  simp

@[congr]
theorem HetT.pmap_congr {m : Type w → Type w'} {α : Type u} {β : Type v} [Monad m]
    [LawfulMonad m] {x y : HetT m α} {f : (a : α) → _ → β} (h : x = y) :
    x.pmap f = y.pmap (fun a ha => f a (h ▸ ha)) := by
  cases h
  simp

protected theorem HetT.pmap_map {m : Type w → Type w'} [Monad m] [LawfulMonad m]
    {α : Type u} {β : Type v} {γ : Type x}
    {x : HetT m α} {f : α → β} {g : (b : β) → (x.map f).Property b → γ} :
    (x.map f).pmap g = x.pmap (fun a ha => g (f a) ⟨a, ha, rfl⟩) := by
  simp only [HetT.map_eq_pure_bind, ext_iff, prun_pmap, prun_bind, Function.comp_apply, prun_pure,
    implies_true, property_pmap, property_bind, property_pure, exists_prop, and_true]
  ext c
  constructor
  · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    exact ⟨a, ha, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨_, ⟨a, ha, rfl⟩, rfl⟩

protected theorem HetT.map_pmap {m : Type w → Type w'} [Monad m] [LawfulMonad m]
    {α : Type u} {β : Type v} {γ : Type x}
    {x : HetT m α} {f : (a : α) → (ha : x.Property a) → β} {g : β → γ} :
    (x.pmap f).map g = x.pmap (fun a ha => g (f a ha)) := by
  simp only [HetT.map_eq_pure_bind, ext_iff, prun_bind, Function.comp_apply, prun_pure, prun_pmap,
    implies_true, property_bind, property_pmap, property_pure, exists_prop, and_true]
  ext c
  constructor
  · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    exact ⟨a, ha, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨_, ⟨a, ha, rfl⟩, rfl⟩

instance [Monad m] [LawfulMonad m] : LawfulMonad (HetT m) where
  map_const {α β} := by ext a x; simp [Functor.mapConst, Functor.map]
  id_map {α} x := by simp [Functor.map]
  comp_map {α β γ} g h := by intro x; simp [Functor.map, HetT.ext_iff];
  seqLeft_eq {α β} x y := by simp [SeqLeft.seqLeft, Functor.map, Seq.seq, HetT.ext_iff];
  seqRight_eq {α β} x y := by simp [Seq.seq, SeqRight.seqRight, Functor.map]
  pure_seq g x := by simp [Seq.seq, Functor.map, Pure.pure]
  bind_pure_comp f x := by simp [Functor.map, Bind.bind, Pure.pure, HetT.ext_iff]
  bind_map f x := by simp [Seq.seq, Functor.map, Bind.bind]
  pure_bind x f := HetT.pure_bind
  bind_assoc x f g := HetT.bind_assoc

@[simp]
theorem HetT.property_map {m : Type w → Type w'} [Functor m] {α : Type u} {β : Type v}
    {x : HetT m α} {f : α → β} {b : β} :
    (x.map f).Property b ↔ (∃ a, f a = b ∧ x.Property a) := by
  simp only [HetT.map]
  apply Iff.intro
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, rfl, ha⟩
  · rintro ⟨a, rfl, ha⟩
    exact ⟨a, ha, rfl⟩

@[simp]
theorem HetT.liftInner_bind {m : Type w → Type w'} {n : Type w → Type w''} {α : Type u}
    {β : Type v} [Monad m] [Monad n] [MonadLiftT m n] [LawfulMonadLiftT m n]
    [LawfulMonad m] [LawfulMonad n] {x : HetT m α} {f : α → HetT m β} :
    (x.bind f).liftInner n = (x.liftInner n).bind (fun a => (f a).liftInner n) := by
  simp only [ext_iff, property_liftInner, prun_bind, property_bind, exists_true_left]
  intro β g
  simp [liftInner, prun, HetT.bind]

end Std.Iterators

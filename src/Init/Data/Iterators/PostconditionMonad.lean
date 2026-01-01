/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Init.Control.Lawful.Basic
public import Init.Data.Subtype.Basic
public import Init.PropLemmas
public import Init.Control.Lawful.MonadLift.Basic

public section

namespace Std.Iterators

/--
`PostconditionT m α` represents an operation in the monad `m` together with a
intrinsic proof that some postcondition holds for the `α` valued monadic result.
It consists of a predicate `P` about `α` and an element of `m ({ a // P a })` and is a helpful tool
for intrinsic verification, notably termination proofs, in the context of iterators.

`PostconditionT m` is a monad if `m` is. However, note that `PostconditionT m α` is a structure,
so that the compiler will generate inefficient code from recursive functions returning
`PostconditionT m α`. Optimizations for `ReaderT`, `StateT` etc. aren't applicable for structures.

Moreover, `PostconditionT m α` is not a well-behaved monad transformer because `PostconditionT.lift`
neither commutes with `pure` nor with `bind`.
-/
@[unbox]
structure PostconditionT (m : Type w → Type w') (α : Type w) where
  /--
  A predicate that holds for the return value(s) of the `m`-monadic operation.
  -/
  Property : α → Prop

  /--
  The actual monadic operation. Its return value is bundled together with a proof that
  it satisfies `Property`.
  -/
  operation : m (Subtype Property)

/--
Lifts an operation from `m` to `PostconditionT m` without asserting any nontrivial postcondition.

Caution: `lift` is not a lawful lift function.
For example, `pure a : PostconditionT m α` is not the same as
`PostconditionT.lift (pure a : m α)`.
-/
@[always_inline, inline, expose]
def PostconditionT.lift {α : Type w} {m : Type w → Type w'} [Functor m] (x : m α) :
    PostconditionT m α :=
  ⟨fun _ => True, (⟨·, .intro⟩) <$> x⟩

@[always_inline, inline, expose]
def PostconditionT.attachLift {α : Type w} {m : Type w → Type w'} [MonadAttach m]
    (x : m α) : PostconditionT m α :=
  ⟨MonadAttach.CanReturn x, MonadAttach.attach x⟩

@[always_inline, inline, expose]
protected def PostconditionT.pure {m : Type w → Type w'} [Pure m] {α : Type w}
    (a : α) : PostconditionT m α :=
  ⟨fun y => a = y, pure <| ⟨a, rfl⟩⟩

/--
Lifts a monadic value from `m { a : α // P a }` to a value `PostconditionT m α`.
-/
@[always_inline, inline]
def PostconditionT.liftWithProperty {α : Type w} {m : Type w → Type w'} {P : α → Prop}
    (x : m { α // P α }) : PostconditionT m α :=
  ⟨P, x⟩

/--
Given a function `f : α → β`, returns a function `PostconditionT m α → PostconditionT m β`,
turning `PostconditionT m` into a functor.

The postcondition of the `x.map f` states that the return value is the image under `f` of some
`a : α` satisfying the `x.Property`.
-/
@[always_inline, inline, expose]
protected def PostconditionT.map {m : Type w → Type w'} [Functor m] {α : Type w} {β : Type w}
    (f : α → β) (x : PostconditionT m α) : PostconditionT m β :=
  ⟨fun b => ∃ a : Subtype x.Property, f a.1 = b,
    (fun a => ⟨f a.val, _, rfl⟩) <$> x.operation⟩

/--
Given a function `α → PostconditionT m β`, returns a function
`PostconditionT m α → PostconditionT m β`, turning `PostconditionT m` into a monad.
-/
@[always_inline, inline, expose]
protected def PostconditionT.bind {m : Type w → Type w'} [Monad m] {α : Type w} {β : Type w}
    (x : PostconditionT m α) (f : α → PostconditionT m β) : PostconditionT m β :=
  ⟨fun b => ∃ a, x.Property a ∧ (f a).Property b,
    x.operation >>= fun a =>
      (fun b =>
        ⟨b.val, a.val, a.property, b.property⟩) <$> (f a).operation⟩

/--
A version of `bind` that provides a proof of the previous postcondition to the mapping function.
-/
@[always_inline, inline]
protected def PostconditionT.pbind {m : Type w → Type w'} [Monad m] {α : Type w} {β : Type w}
    (x : PostconditionT m α) (f : Subtype x.Property → PostconditionT m β) : PostconditionT m β :=
  ⟨fun b => ∃ a, (f a).Property b,
    x.operation >>= fun a => (fun b => ⟨b.val, a, b.property⟩) <$> (f a).operation⟩

/--
Lifts an operation from `m` to `PostConditionT m` and then applies `PostconditionT.map`.
-/
@[always_inline, inline]
protected def PostconditionT.liftMap {m : Type w → Type w'} [Monad m] {α : Type w} {β : Type w}
    (f : α → β) (x : m α) : PostconditionT m β :=
  ⟨fun b => ∃ a, f a = b, (fun a => ⟨f a, a, rfl⟩) <$> x⟩

/--
Converts an operation from `PostConditionT m` to `m`, discarding the postcondition.
-/
@[always_inline, inline]
def PostconditionT.run {m : Type w → Type w'} [Monad m] {α : Type w} (x : PostconditionT m α) :
    m α :=
  (fun a => a.val) <$> x.operation

theorem PostconditionT.run_eq_map {m : Type w → Type w'} [Monad m] {α : Type w}
    {x : PostconditionT m α} :
    x.run = Subtype.val <$> x.operation :=
  (rfl)

instance {m : Type w → Type w'} [Functor m] : Functor (PostconditionT m) where
  map := PostconditionT.map

instance {m : Type w → Type w'} [Monad m] : Monad (PostconditionT m) where
  pure := PostconditionT.pure
  bind := PostconditionT.bind

theorem PostconditionT.pure_eq_pure {m : Type w → Type w'} [Monad m] {α} {a : α} :
    pure a = PostconditionT.pure (m := m) a :=
  rfl

@[simp]
theorem PostconditionT.property_pure {m : Type w → Type w'} [Monad m] {α : Type w}
    {x : α} :
    (pure x : PostconditionT m α).Property = (x = ·) := by
  rfl

@[simp]
theorem PostconditionT.operation_pure {m : Type w → Type w'} [Monad m] {α : Type w}
    {x : α} :
    (pure x : PostconditionT m α).operation = pure ⟨x, property_pure (m := m) ▸ rfl⟩ := by
  rfl

theorem PostconditionT.ext {m : Type w → Type w'} [Monad m] [LawfulMonad m]
    {α : Type w} {x y : PostconditionT m α}
    (h : x.Property = y.Property) (h' : (fun p => ⟨p.1, h ▸ p.2⟩) <$> x.operation = y.operation) :
    x = y := by
  cases x; cases y; cases h
  simpa using h'

theorem PostconditionT.ext_iff {m : Type w → Type w'} [Monad m] [LawfulMonad m]
    {α : Type w} {x y : PostconditionT m α} :
    x = y ↔ ∃ h : x.Property = y.Property, (fun p => ⟨p.1, h ▸ p.2⟩) <$> x.operation = y.operation := by
  constructor
  · rintro rfl
    exact ⟨rfl, by simp⟩
  · rintro ⟨h, h'⟩
    exact PostconditionT.ext h h'

@[simp]
protected theorem PostconditionT.map_eq_pure_bind {m : Type w → Type w'} [Monad m] [LawfulMonad m]
    {α : Type w} {β : Type w} {f : α → β} {x : PostconditionT m α} :
    x.map f = x.bind (pure ∘ f) := by
  apply PostconditionT.ext <;> simp [PostconditionT.map, PostconditionT.bind]

@[simp]
protected theorem PostconditionT.pure_bind {m : Type w → Type w'} [Monad m] [LawfulMonad m]
    {α : Type w} {β : Type w} {f : α → PostconditionT m β} {a : α} :
    (pure a : PostconditionT m α).bind f = f a := by
  apply PostconditionT.ext <;> simp [pure, PostconditionT.pure, PostconditionT.bind]

@[simp]
protected theorem PostconditionT.bind_pure {m : Type w → Type w'} [Monad m] [LawfulMonad m]
    {α : Type w} {x : PostconditionT m α} :
    x.bind pure = x := by
  apply PostconditionT.ext <;> simp [pure, PostconditionT.pure, PostconditionT.bind]

@[simp]
protected theorem PostconditionT.bind_assoc {m : Type w → Type w'} [Monad m] [LawfulMonad m]
    {α β γ: Type w} {x : PostconditionT m α} {f : α → PostconditionT m β} {g : β → PostconditionT m γ} :
    (x.bind f).bind g = x.bind (fun a => (f a).bind g) := by
  apply PostconditionT.ext
  · simp [PostconditionT.bind]
  · simp only [PostconditionT.bind, bind_assoc, bind_map_left, map_bind, Functor.map_map]
    ext c
    constructor
    · rintro ⟨b, ⟨a, ha, hb⟩, h⟩
      exact ⟨a, ha, b, hb, h⟩
    · rintro ⟨a, ha, b, hb, h⟩
      exact ⟨b, ⟨a, ha, hb⟩, h⟩

@[simp]
protected theorem PostconditionT.map_pure {m : Type w → Type w'} [Monad m] [LawfulMonad m]
    {α : Type w} {β : Type w} {f : α → β} {a : α} :
    (pure a : PostconditionT m α).map f = pure (f a) := by
  apply PostconditionT.ext <;> simp [pure, PostconditionT.map, PostconditionT.pure]

instance [Monad m] [LawfulMonad m] : LawfulMonad (PostconditionT m) where
  map_const {α β} := by ext a x; simp [Functor.mapConst, Functor.map]
  id_map {α} x := by simp [Functor.map]
  comp_map {α β γ} g h := by intro x; simp [Functor.map]; rfl
  seqLeft_eq {α β} x y := by simp [SeqLeft.seqLeft, Functor.map, Seq.seq]; rfl
  seqRight_eq {α β} x y := by simp [Seq.seq, SeqRight.seqRight, Functor.map]
  pure_seq g x := by simp [Seq.seq, Functor.map]
  bind_pure_comp f x := by simp [Functor.map, Bind.bind]; rfl
  bind_map f x := by simp [Seq.seq, Functor.map]; rfl
  pure_bind x f := PostconditionT.pure_bind
  bind_assoc x f g := PostconditionT.bind_assoc

@[simp]
theorem PostconditionT.property_map {m : Type w → Type w'} [Functor m] {α : Type w} {β : Type w}
    {x : PostconditionT m α} {f : α → β} {b : β} :
    (x.map f).Property b ↔ (∃ a, f a = b ∧ x.Property a) := by
  simp only [PostconditionT.map]
  apply Iff.intro
  · rintro ⟨⟨a, ha⟩, h⟩
    exact ⟨a, h, ha⟩
  · rintro ⟨a, h, ha⟩
    exact ⟨⟨a, ha⟩, h⟩

@[simp]
theorem PostconditionT.operation_map {m : Type w → Type w'} [Functor m] {α : Type w} {β : Type w}
    {x : PostconditionT m α} {f : α → β} :
    (x.map f).operation =
      (fun a => ⟨_, (property_map (m := m)).mpr ⟨a.1, rfl, a.2⟩⟩) <$> x.operation := by
  rfl

@[simp]
theorem PostconditionT.operation_bind {m : Type w → Type w'} [Monad m] {α : Type w} {β : Type w}
    {x : PostconditionT m α} {f : α → PostconditionT m β} :
    (x.bind f).operation = (do
      let a ← x.operation
      (fun fa => ⟨fa.1, by exact⟨a.1, a.2, fa.2⟩⟩) <$> (f a.1).operation) := by
  rfl

theorem PostconditionT.operation_bind' {m : Type w → Type w'} [Monad m] {α : Type w} {β : Type w}
    {x : PostconditionT m α} {f : α → PostconditionT m β} :
    (x >>= f).operation = (do
      let a ← x.operation
      (fun fa => ⟨fa.1, by exact⟨a.1, a.2, fa.2⟩⟩) <$> (f a.1).operation) := by
  rfl

theorem PostconditionT.operation_eq_map_mk_operation {m : Type w → Type w'}
    [Monad m] [LawfulMonad m] {x : PostconditionT m α} :
    x.operation = (fun a => ⟨a.val, a.property⟩) <$> x.operation := by
  simp

theorem PostconditionT.operation_bind_eq_operation_bind_mk {m : Type w → Type w'}
    [Monad m] {x : PostconditionT m α} {f : Subtype x.Property → m β} :
    x.operation >>= f = x.operation >>= (fun a => f ⟨a.val, a.property⟩) := by
  rfl

@[simp]
theorem PostconditionT.run_bind {m : Type w → Type w'} [Monad m] [LawfulMonad m]
    {α : Type w} {β : Type w} {x : PostconditionT m α} {f : α → PostconditionT m β} :
    (x.bind f).run = x.run >>= (f · |>.run) := by
  simp [run_eq_map]

@[simp]
theorem PostconditionT.run_bind' {m : Type w → Type w'} [Monad m] [LawfulMonad m]
    {α : Type w} {β : Type w} {x : PostconditionT m α} {f : α → PostconditionT m β} :
    (x >>= f).run = x.run >>= (f · |>.run) :=
  run_bind

@[simp]
theorem PostconditionT.property_lift {m : Type w → Type w'} [Functor m] {α : Type w}
    {x : m α} : (lift x : PostconditionT m α).Property = (fun _ => True) := by
  rfl

@[simp]
theorem PostconditionT.operation_lift {m : Type w → Type w'} [Functor m] {α : Type w}
    {x : m α} : (lift x : PostconditionT m α).operation =
      (⟨·, property_lift (m := m) ▸ True.intro⟩) <$> x := by
  rfl

@[simp]
theorem PostconditionT.run_attachLift {m : Type w → Type w'} [Monad m] [MonadAttach m]
    [WeaklyLawfulMonadAttach m] {α : Type w}
    {x : m α} : (attachLift x).run = x := by
  simp [attachLift, run_eq_map, WeaklyLawfulMonadAttach.map_attach]

@[simp]
theorem PostconditionT.operation_attachLift {m : Type w → Type w'} [Monad m] [MonadAttach m]
    {α : Type w} {x : m α} : (attachLift x : PostconditionT m α).operation =
      MonadAttach.attach x := by
  rfl

instance {m : Type w → Type w'} {n : Type w → Type w''} [MonadLift m n] :
    MonadLift (PostconditionT m) (PostconditionT n) where
  monadLift x := ⟨_, monadLift x.operation⟩

instance PostconditionT.instLawfulMonadLift {m : Type w → Type w'} {n : Type w → Type w''}
    [MonadLift m n] [Monad m] [Monad n] [LawfulMonad m] [LawfulMonad n] [LawfulMonadLift m n] :
    LawfulMonadLift (PostconditionT m) (PostconditionT n) where
  monadLift_pure a := by
    simp [MonadLift.monadLift, monadLift, LawfulMonadLift.monadLift_pure, pure,
      PostconditionT.pure]
  monadLift_bind x f := by
    simp only [MonadLift.monadLift, bind, monadLift, LawfulMonadLift.monadLift_bind,
      PostconditionT.bind, mk.injEq, heq_eq_eq, true_and]
    simp only [map_eq_pure_bind, LawfulMonadLift.monadLift_bind, LawfulMonadLift.monadLift_pure]

end Std.Iterators

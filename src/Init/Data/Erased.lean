/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Julia Markus Himmel
-/
module

prelude
public import Init.Classical
public import Init.Control.Lawful.Basic
import Init.Ext

@[expose] public section

set_option linter.missingDocs true

/-!
# Erased data

This file defines `Erased`, a type that tracks data in the logic without retaining it at runtime,
and `NSigma`, a dependent pair whose first component is erased.
-/

universe u v

/--
`Erased α` is classically isomorphic to `α`, but its values are erased by the compiler in the same
way as types and proofs. It can be used to track data without storing it at runtime.
-/
def Erased (α : Sort u) : Sort max 1 u :=
  { s : α → Prop // ∃ a, (a = ·) = s }

namespace Erased

/-- Erases a value. -/
@[macro_inline]
def mk {α} (a : α) : Erased α :=
  ⟨fun b => a = b, a, rfl⟩

/-- Extracts an erased value noncomputably. -/
noncomputable def out {α} : Erased α → α
  | ⟨_, h⟩ => Classical.choose h

/--
Extracts an erased value when it is a type.

`(mk a).OutType` is not definitionally equal to `a`.
-/
abbrev OutType (a : Erased (Sort u)) : Sort u :=
  out a

/-- Extracts an erased value when it is a proof. -/
theorem out_proof {p : Prop} (a : Erased p) : p :=
  out a

@[simp]
theorem out_mk {α} (a : α) : (mk a).out = a := by
  let h := (mk a).2
  change Classical.choose h = a
  have := Classical.choose_spec h
  exact cast (congrFun this a).symm rfl

@[simp]
theorem mk_out {α} : ∀ a : Erased α, mk a.out = a
  | ⟨s, h⟩ => by
    simp only [mk]
    congr
    exact Classical.choose_spec h

@[ext]
theorem out_inj {α} {a b : Erased α} (h : a.out = b.out) : a = b := by
  simpa using congrArg mk h

instance (α : Type u) : Repr (Erased α) :=
  ⟨fun _ _ => "Erased"⟩

instance (α : Type u) : ToString (Erased α) :=
  ⟨fun _ => "Erased"⟩

/-- Computably produces an erased value from a proof of nonemptiness. -/
def choice {α} (h : Nonempty α) : Erased α :=
  mk (Classical.choice h)

@[simp]
theorem nonempty_iff {α} : Nonempty (Erased α) ↔ Nonempty α :=
  ⟨fun ⟨a⟩ => ⟨a.out⟩, fun ⟨a⟩ => ⟨mk a⟩⟩

instance {α} [h : Nonempty α] : Inhabited (Erased α) :=
  ⟨choice h⟩

/--
The bind operation on `Erased`. This is universe-polymorphic, unlike the operation from `Monad`.
-/
def bind {α β} (a : Erased α) (f : α → Erased β) : Erased β :=
  ⟨fun b => (f a.out).1 b, (f a.out).2⟩

@[simp]
theorem bind_eq_out {α β} (a f) : @bind α β a f = f a.out :=
  rfl

/-- Collapses two levels of erasure. -/
def join {α} (a : Erased (Erased α)) : Erased α :=
  bind a id

@[simp]
theorem join_eq_out {α} (a) : @join α a = a.out :=
  rfl

/--
The map operation on `Erased`. This is universe-polymorphic, unlike the operation from `Functor`.
-/
def map {α β} (f : α → β) (a : Erased α) : Erased β :=
  bind a (mk ∘ f)

@[simp]
theorem map_out {α β} {f : α → β} (a : Erased α) : (a.map f).out = f a.out := by
  simp [map]

protected instance Monad : Monad Erased where
  pure := @mk
  bind := @bind
  map := @map

@[simp]
theorem pure_def {α} : (pure : α → Erased α) = @mk _ :=
  rfl

@[simp]
theorem bind_def {α β} : ((· >>= ·) : Erased α → (α → Erased β) → Erased β) = @bind _ _ :=
  rfl

@[simp]
theorem map_def {α β} : ((· <$> ·) : (α → β) → Erased α → Erased β) = @map _ _ :=
  rfl

protected instance instLawfulMonad : LawfulMonad Erased :=
  { id_map := by intros; ext; simp
    map_const := by intros; ext; simp [Functor.mapConst]
    pure_bind := by intros; ext; simp
    bind_assoc := by intros; ext; simp
    bind_pure_comp := by intros; ext; simp
    bind_map := by intros; ext; simp [Seq.seq]
    seqLeft_eq := by intros; ext; simp [Seq.seq, SeqLeft.seqLeft]
    seqRight_eq := by intros; ext; simp [Seq.seq, SeqRight.seqRight]
    pure_seq := by intros; ext; simp [Seq.seq] }

end Erased

/--
Dependent pairs whose first component is erased at runtime.

`NSigma β` is logically analogous to `Sigma β`, but its runtime representation is exactly the
representation of its second component. Consequently, `fst` is noncomputable while `snd` is
computable and does not add indirection.
-/
structure NSigma {α : Type u} (β : α → Type v) where
  /-- Internal constructor. Use `NSigma.mk` to construct an `NSigma` from its unerased first value. -/
  intro ::
  /-- The erased representation of the first component. Use `NSigma.fst` to recover its value. -/
  erasedFst : Erased α
  /-- The second component of the dependent pair. -/
  snd : β erasedFst.out

namespace NSigma

/-- Constructs a dependent pair whose first component will be erased. -/
@[macro_inline]
def mk {α : Type u} {β : α → Type v} (a : α) (b : β a) : NSigma β :=
  .intro (.mk a) ((Erased.out_mk a).symm ▸ b)

/-- The first component of an `NSigma`, recovered noncomputably. -/
noncomputable abbrev fst {α : Type u} {β : α → Type v} (x : NSigma β) : α :=
  x.erasedFst.out

@[simp]
theorem fst_mk {α : Type u} {β : α → Type v} (a : α) (b : β a) : (mk a b).fst = a :=
  by
    simp [fst, mk]

end NSigma

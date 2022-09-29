/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Classical
import Init.Control.EState
import Init.Control.Reader

def EST (ε : Type) (σ : Type) : Type → Type := EStateM ε σ
abbrev ST (σ : Type) := EST Empty σ

instance (ε σ : Type) : Monad (EST ε σ) := inferInstanceAs (Monad (EStateM _ _))
instance (ε σ : Type) : MonadExceptOf ε (EST ε σ) := inferInstanceAs (MonadExceptOf ε (EStateM _ _))
instance {ε σ : Type} {α : Type} [Inhabited ε] : Inhabited (EST ε σ α) := inferInstanceAs (Inhabited (EStateM _ _ _))
instance (σ : Type) : Monad (ST σ) := inferInstanceAs (Monad (EST _ _))

-- Auxiliary class for inferring the "state" of `EST` and `ST` monads
class STWorld (σ : outParam Type) (m : Type → Type)

instance {σ m n} [MonadLift m n] [STWorld σ m] : STWorld σ n := ⟨⟩
instance {ε σ} : STWorld σ (EST ε σ) := ⟨⟩

@[noinline, nospecialize]
def runEST {ε α : Type} (x : (σ : Type) → EST ε σ α) : Except ε α :=
  match x Unit () with
  | EStateM.Result.ok a _     => Except.ok a
  | EStateM.Result.error ex _ => Except.error ex

@[noinline, nospecialize]
def runST {α : Type} (x : (σ : Type) → ST σ α) : α :=
  match x Unit () with
  | EStateM.Result.ok a _     => a
  | EStateM.Result.error ex _ => nomatch ex

@[always_inline]
instance {ε σ} : MonadLift (ST σ) (EST ε σ) := ⟨fun x s =>
  match x s with
  | EStateM.Result.ok a s     => EStateM.Result.ok a s
  | EStateM.Result.error ex _ => nomatch ex⟩

namespace ST

/-- References -/
opaque RefPointed : NonemptyType.{0}

structure Ref (σ : Type) (α : Type) : Type where
  ref : RefPointed.type
  h   : Nonempty α

instance {σ α} [s : Nonempty α] : Nonempty (Ref σ α) :=
  Nonempty.intro { ref := Classical.choice RefPointed.property, h := s }

namespace Prim

/-- Auxiliary definition for showing that `ST σ α` is inhabited when we have a `Ref σ α` -/
private noncomputable def inhabitedFromRef {σ α} (r : Ref σ α) : ST σ α :=
  let _ : Inhabited α := Classical.inhabited_of_nonempty r.h
  pure default

@[extern "lean_st_mk_ref"]
opaque mkRef {σ α} (a : α) : ST σ (Ref σ α) := pure { ref := Classical.choice RefPointed.property, h := Nonempty.intro a }
@[extern "lean_st_ref_get"]
opaque Ref.get {σ α} (r : @& Ref σ α) : ST σ α := inhabitedFromRef r
@[extern "lean_st_ref_set"]
opaque Ref.set {σ α} (r : @& Ref σ α) (a : α) : ST σ Unit
@[extern "lean_st_ref_swap"]
opaque Ref.swap {σ α} (r : @& Ref σ α) (a : α) : ST σ α := inhabitedFromRef r
@[extern "lean_st_ref_take"]
unsafe opaque Ref.take {σ α} (r : @& Ref σ α) : ST σ α := inhabitedFromRef r
@[extern "lean_st_ref_ptr_eq"]
opaque Ref.ptrEq {σ α} (r1 r2 : @& Ref σ α) : ST σ Bool

@[inline] unsafe def Ref.modifyUnsafe {σ α : Type} (r : Ref σ α) (f : α → α) : ST σ Unit := do
  let v ← Ref.take r
  Ref.set r (f v)

@[inline] unsafe def Ref.modifyGetUnsafe {σ α β : Type} (r : Ref σ α) (f : α → β × α) : ST σ β := do
  let v ← Ref.take r
  let (b, a) := f v
  Ref.set r a
  pure b

@[implemented_by Ref.modifyUnsafe]
def Ref.modify {σ α : Type} (r : Ref σ α) (f : α → α) : ST σ Unit := do
  let v ← Ref.get r
  Ref.set r (f v)

@[implemented_by Ref.modifyGetUnsafe]
def Ref.modifyGet {σ α β : Type} (r : Ref σ α) (f : α → β × α) : ST σ β := do
  let v ← Ref.get r
  let (b, a) := f v
  Ref.set r a
  pure b

end Prim

section
variable {σ : Type} {m : Type → Type} [Monad m] [MonadLiftT (ST σ) m]

@[inline] def mkRef {α : Type} (a : α) : m (Ref σ α) :=  liftM <| Prim.mkRef a
@[inline] def Ref.get {α : Type} (r : Ref σ α) : m α := liftM <| Prim.Ref.get r
@[inline] def Ref.set {α : Type} (r : Ref σ α) (a : α) : m Unit := liftM <| Prim.Ref.set r a
@[inline] def Ref.swap {α : Type} (r : Ref σ α) (a : α) : m α := liftM <| Prim.Ref.swap r a
@[inline] unsafe def Ref.take {α : Type} (r : Ref σ α) : m α := liftM <| Prim.Ref.take r
@[inline] def Ref.ptrEq {α : Type} (r1 r2 : Ref σ α) : m Bool := liftM <| Prim.Ref.ptrEq r1 r2
@[inline] def Ref.modify {α : Type} (r : Ref σ α) (f : α → α) : m Unit := liftM <| Prim.Ref.modify r f
@[inline] def Ref.modifyGet {α : Type} {β : Type} (r : Ref σ α) (f : α → β × α) : m β := liftM <| Prim.Ref.modifyGet r f

def Ref.toMonadStateOf (r : Ref σ α) : MonadStateOf α m where
  get := r.get
  set := r.set
  modifyGet := r.modifyGet

end

end ST

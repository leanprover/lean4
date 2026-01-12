/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Init.Classical
public import Init.Control.EState
public import Init.Control.Reader

public section

opaque Void.nonemptyType (σ : Type) : NonemptyType.{0}

@[expose] def Void (σ : Type) : Type := Void.nonemptyType σ |>.type

instance Void.instNonempty : Nonempty (Void σ) :=
  by exact (Void.nonemptyType σ).property

@[extern "lean_void_mk"]
opaque Void.mk (x : σ) : Void σ

structure ST.Out (σ : Type) (α : Type) where
  val : α
  state : Void σ

/--
A restricted version of `IO` in which mutable state is the only side effect.

It is possible to run `ST` computations in a non-monadic context using `runST`.
-/
@[expose] def ST (σ : Type) (α : Type) := Void σ → ST.Out σ α

namespace ST

@[always_inline, inline]
protected def pure (x : α) : ST σ α := fun s => .mk x s

@[always_inline, inline]
protected def bind (x : ST σ α) (f : α → ST σ β) : ST σ β :=
  fun s =>
    match x s with
    | .mk x s => f x s

end ST

instance (σ : Type) : Monad (ST σ) where
  pure := ST.pure
  bind := ST.bind

@[always_inline]
instance : MonadFinally (ST σ) where
  tryFinally' x f := fun s =>
    match x s with
    | .mk x s =>
      match f (some x) s with
      | .mk y s => .mk (x, y) s

instance {σ : Type} {α : Type} [Inhabited α] : Inhabited (ST σ α) where
  default := fun s => .mk default s

instance {σ : Type} : MonadAttach (ST σ) where
  CanReturn x a := ∃ s s', x s = ⟨a, s'⟩
  attach x s := match h : x s with | ⟨a, s'⟩ => ⟨⟨a, s, s', h⟩, s'⟩

inductive EST.Out (ε : Type) (σ : Type) (α : Type) where
  | ok : α → Void σ → EST.Out ε σ α
  | error : ε → Void σ → EST.Out ε σ α

/--
A restricted version of `IO` in which mutable state and exceptions are the only side effects.

It is possible to run `EST` computations in a non-monadic context using `runEST`.
-/
@[expose] def EST (ε : Type) (σ : Type) (α : Type) : Type := Void σ → EST.Out ε σ α

namespace EST

@[always_inline, inline]
protected def pure (a : α) : EST ε σ α := fun s => .ok a s

@[always_inline, inline]
protected def bind (x : EST ε σ α) (f : α → EST ε σ β) : EST ε σ β :=
  fun s => match x s with
  | .ok a s    => f a s
  | .error e s => .error e s

@[always_inline, inline]
protected def throw (e : ε) : EST ε σ α := fun s => .error e s

@[always_inline, inline]
protected def tryCatch (x : EST ε σ α) (handle : ε → EST ε σ α) : EST ε σ α :=
  fun s => match x s with
  | .ok a s => .ok a s
  | .error e s => handle e s

end EST

instance (ε σ : Type) : Monad (EST ε σ) where
  pure := EST.pure
  bind := EST.bind

@[always_inline]
instance : MonadFinally (EST ε σ) where
  tryFinally' x f := fun s =>
    let r := x s
    match r with
    | .ok x s =>
      match f (some x) s with
      | .ok y s => .ok (x, y) s
      | .error e s => .error e s
    | .error e s =>
      match f none s with
      | .ok _ s => .error e s
      | .error e s => .error e s

instance {ε σ : Type} : MonadAttach (EST ε σ) where
  CanReturn x a := ∃ s s', x s = .ok a s'
  attach x s := match h : x s with
    | .ok a s' => .ok ⟨a, s, s', h⟩ s'
    | .error e s' => .error e s'

instance (ε σ : Type) : MonadExceptOf ε (EST ε σ) where
  throw := EST.throw
  tryCatch := EST.tryCatch

instance {ε σ : Type} {α : Type} [Inhabited ε] : Inhabited (EST ε σ α) where
  default := fun s => .error default s

/--
An auxiliary class used to infer the “state” of `EST` and `ST` monads.
-/
class STWorld (σ : outParam Type) (m : Type → Type)

instance {σ m n} [MonadLift m n] [STWorld σ m] : STWorld σ n := ⟨⟩
instance {σ} : STWorld σ (ST σ) := ⟨⟩
instance {ε σ} : STWorld σ (EST ε σ) := ⟨⟩

/--
Runs an `EST` computation, in which mutable state and exceptions are the only side effects.
-/
@[noinline, nospecialize]
def runEST {ε α : Type} (x : (σ : Type) → EST ε σ α) : Except ε α :=
  match x Unit (Void.mk ()) with
  | .ok a _     => Except.ok a
  | .error ex _ => Except.error ex

/--
Runs an `ST` computation, in which mutable state via `ST.Ref` is the only side effect.
-/
@[noinline, nospecialize]
def runST {α : Type} (x : (σ : Type) → ST σ α) : α :=
  match x Unit (Void.mk ()) with
  | .mk a _ => a

@[always_inline]
instance {ε σ} : MonadLift (ST σ) (EST ε σ) := ⟨fun x s =>
  match x s with
  | .mk a s => .ok a s⟩

namespace ST

/-- References -/
opaque RefPointed : NonemptyType.{0}

/--
Mutable reference cells that contain values of type `α`. These cells can read from and mutated in
the `ST σ` monad.
-/
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

/--
Creates a new mutable reference that contains the provided value `a`.
-/
@[inline] def mkRef {α : Type} (a : α) : m (Ref σ α) :=  liftM <| Prim.mkRef a
/--
Reads the value of a mutable reference.
-/
@[inline] def Ref.get {α : Type} (r : Ref σ α) : m α := liftM <| Prim.Ref.get r
/--
Replaces the value of a mutable reference.
-/
@[inline] def Ref.set {α : Type} (r : Ref σ α) (a : α) : m Unit := liftM <| Prim.Ref.set r a
/--
Atomically swaps the value of a mutable reference cell with another value. The reference cell's
original value is returned.
-/
@[inline] def Ref.swap {α : Type} (r : Ref σ α) (a : α) : m α := liftM <| Prim.Ref.swap r a
/--
Reads the value of a mutable reference cell, removing it.

This causes subsequent attempts to read from or take the reference cell to block until a new value
is written using `ST.Ref.set`.
-/
@[inline] unsafe def Ref.take {α : Type} (r : Ref σ α) : m α := liftM <| Prim.Ref.take r
/--
Checks whether two reference cells are in fact aliases for the same cell.

Even if they contain the same value, two references allocated by different executions of `IO.mkRef`
or `ST.mkRef` are distinct. Modifying one has no effect on the other. Likewise, a single reference
cell may be aliased, and modifications to one alias also modify the other.
-/
@[inline] def Ref.ptrEq {α : Type} (r1 r2 : Ref σ α) : m Bool := liftM <| Prim.Ref.ptrEq r1 r2
/--
Atomically modifies a mutable reference cell by replacing its contents with the result of a function
call.
-/
@[inline] def Ref.modify {α : Type} (r : Ref σ α) (f : α → α) : m Unit := liftM <| Prim.Ref.modify r f
/--
Atomically modifies a mutable reference cell by replacing its contents with the result of a function
call that simultaneously computes a value to return.
-/
@[inline] def Ref.modifyGet {α : Type} {β : Type} (r : Ref σ α) (f : α → β × α) : m β := liftM <| Prim.Ref.modifyGet r f

/--
Creates a `MonadStateOf` instance from a reference cell.

This allows programs written against the [state monad](lean-manual://section/state-monads) API to
be executed using a mutable reference cell to track the state.
-/
def Ref.toMonadStateOf (r : Ref σ α) : MonadStateOf α m where
  get := r.get
  set := r.set
  modifyGet := r.modifyGet

end

end ST

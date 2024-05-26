/-
Copyright (c) 2024 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/

namespace Lake

/--
`IO.Result α` represents a value of type `α` extracted from the
`IO` / `BaseIO` monad at a given state of the "real world".

The `IO.RealWorld` component is used to ensure correctness of IO computations
at the Lean level but has no real runtime utility. Therefore, this type is
optimized to represent the value solely as `α` at runtime.
-/
structure IO.Result (α : Type u) where private mk' ::
  private value' : α
  private world' : IO.RealWorld

namespace IO.Result

@[noinline] unsafe def mkImpl (a : α) (_ : IO.RealWorld) : IO.Result α :=
  unsafeCast a

@[implemented_by mkImpl] def mk := @mk'

@[noinline] unsafe def valueImpl (v : IO.Result α) : α :=
  unsafeCast v

@[implemented_by valueImpl] def value := @value'

/-
Without `noinline`, the inlined `PUnit`
will result in closed term extraction of IO actions.
-/
@[noinline] unsafe def worldImpl (_ : IO.Result α) : IO.RealWorld :=
  unsafeCast ()

@[implemented_by worldImpl] def world := @world'

def casesOnImpl
  {motive : IO.Result α → Sort u} (v : IO.Result α)
  (mk : ∀ v w, motive {value' := v, world' := w})
: motive v := mk v.value v.world

attribute [implemented_by casesOnImpl] IO.Result.casesOn

end IO.Result

def BaseIO' (α : Type u) :=
  IO.RealWorld → IO.Result α

namespace BaseIO'

@[inline] protected def pure (a : α) : BaseIO' α :=
  fun w => .mk a w

@[inline] protected def bind (x : BaseIO' α) (f : α → BaseIO' β) : BaseIO' β :=
  fun w => let v := x w; f v.value v.world

instance : Monad BaseIO' where
  pure := BaseIO'.pure
  bind := BaseIO'.bind

@[inline] def ofBaseIO (x : BaseIO α) : BaseIO' α := fun w =>
  match x w with
  | .ok a w => .mk a w

instance : MonadLift BaseIO BaseIO' := ⟨ofBaseIO⟩

@[inline] def toBaseIO (x : BaseIO' α) : BaseIO α := fun w =>
  match x w with
  | .mk v w => .ok v w

--instance : MonadLift BaseIO' BaseIO := ⟨toBaseIO⟩

@[always_inline]
instance : MonadFinally BaseIO' where
  tryFinally' := fun x h => do
   let a ← x
   let b ← h (some a)
   return (a, b)

end BaseIO'

abbrev EIO' (ε) := ExceptT ε BaseIO'

namespace EIO'

@[inline] def toBaseIO' (x : EIO' ε α) : BaseIO' (Except ε α) :=
  x

@[inline] def ofEIO (x : EIO ε α) : EIO' ε α :=
  ExceptT.mk <| BaseIO'.ofBaseIO <| x.toBaseIO

instance : MonadLift (EIO ε) (EIO' ε) := ⟨ofEIO⟩

@[inline] def toEIO (x : EIO' ε α) : EIO ε α := do
  inline <| liftExcept <| ← x.toBaseIO'.toBaseIO

--instance : MonadLift (EIO' ε) (EIO ε) := ⟨toEIO⟩

@[inline] def catchExceptions (h : ε → BaseIO' α) (x : EIO' ε α) : BaseIO' α := do
  match (← x.run) with
  | .ok a => pure a
  | .error e => h e

@[inline] def adaptExcept (f : ε → ε') (x : EIO' ε α) : EIO' ε' α := do
  (← x.run).mapError f

end EIO'

abbrev IO' := EIO' IO.Error

instance : MonadLift IO IO' := ⟨EIO'.ofEIO⟩
--instance : MonadLift IO' IO := ⟨EIO'.toEIO⟩

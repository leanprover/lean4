/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura, Sebastian Ullrich
-/
prelude
import Init.Core

universe u v w

@[reducible] def Functor.mapRev {f : Type u → Type v} [Functor f] {α β : Type u} : f α → (α → β) → f β :=
  fun a f => f <$> a

infixr:100 " <&> " => Functor.mapRev

@[inline] def Functor.discard {f : Type u → Type v} {α : Type u} [Functor f] (x : f α) : f PUnit :=
  Functor.mapConst PUnit.unit x

export Functor (discard)

class Alternative (f : Type u → Type v) extends Applicative f : Type (max (u+1) v) where
  failure : {α : Type u} → f α
  orElse  : {α : Type u} → f α → (Unit → f α) → f α

instance (f : Type u → Type v) (α : Type u) [Alternative f] : OrElse (f α) := ⟨Alternative.orElse⟩

variable {f : Type u → Type v} [Alternative f] {α : Type u}

export Alternative (failure)

@[inline] def guard {f : Type → Type v} [Alternative f] (p : Prop) [Decidable p] : f Unit :=
  if p then pure () else failure

@[inline] def optional (x : f α) : f (Option α) :=
  some <$> x <|> pure none

class ToBool (α : Type u) where
  toBool : α → Bool

export ToBool (toBool)

instance : ToBool Bool where
  toBool b := b

@[macroInline] def bool {β : Type u} {α : Type v} [ToBool β] (f t : α) (b : β) : α :=
  match toBool b with
  | true  => t
  | false => f

@[macroInline] def orM {m : Type u → Type v} {β : Type u} [Monad m] [ToBool β] (x y : m β) : m β := do
  let b ← x
  match toBool b with
  | true  => pure b
  | false => y

infixr:30 " <||> " => orM

@[macroInline] def andM {m : Type u → Type v} {β : Type u} [Monad m] [ToBool β] (x y : m β) : m β := do
  let b ← x
  match toBool b with
  | true  => y
  | false => pure b

infixr:35 " <&&> " => andM

@[macroInline] def notM {m : Type → Type v} [Applicative m] (x : m Bool) : m Bool :=
  not <$> x

/-!

# How `MonadControl` works

There is a [tutorial by Alexis King](https://lexi-lambda.github.io/blog/2019/09/07/demystifying-monadbasecontrol/) that this docstring is based on.

Suppose we have `foo : ∀ α, IO α → IO α` and `bar : StateT σ IO β` (ie, `bar : σ → IO (σ × β)`).
We might want to 'map' `bar` by `foo`. Concretely we would write this as:

```lean
def mapped_foo : StateT σ m β → StateT σ m β := do
  let s ← get
  let (s', v) ← lift <| foo <| StateT.run bar s
  set s'
  pure v
```

This is fine but it's not going to generalise, what if we replace `StateT Nat IO` with a large tower of monad transformers?
We would have to rewrite the above to handle each of the `run` functions for each transformer in the stack.

Is there a way to generalise `run` as a kind of inverse of `lift`?
We have `lift : m α → StateT σ m α` for all `m`, but we also need to 'unlift' the state.
But `unlift : StateT σ IO α → IO α` can't be implemented. So we need something else.

If we look at the definition of `mapped_foo`, we see that `lift <| foo <| StateT.run bar s`
has the type `IO (σ × β)`. The key idea is that `σ × β` contains all of the information needed to reconstruct the state and the new value.

Now lets define some values to generalise `mapped_foo`:
- Write `IO (σ × β)` as `IO (stM β)`
- Write `StateT.run . s` as `mapInBase : StateT σ IO α → IO (stM β)`
- Define `restoreM : IO (stM α) → StateT σ IO α` as `fun x => do let (s', v) ← lift x; set s'; pure v`

To get

```lean
def mapped_foo : StateT σ m β → StateT σ m β := do
  let s ← get
  let mapInBase := fun z => StateT.run z s
  restoreM <| foo <| mapInBase bar
```

and finally define

```lean
control : {α : Type u} → (({β : Type u} → StateT σ IO β → IO (stM β)) → IO (stM α)) → StateT σ IO α
  | α, f => do
    let s ← get
    let mapInBase := fun {β} (z : StateT σ IO β) => StateT.run z s
    let r : IO (stM α) := f mapInBase
    restoreM r
```

now we can write `mapped_foo` as:

```lean
def mapped_foo : StateT σ m β → StateT σ m β :=
  control fun mapInBase => foo (mapInBase bar)
```

The core idea of `mapInBase` is that given any `β`, it runs an instance of
`StateT σ IO β` and 'packages' the result and state as  `IO (stM β)` so that it can be piped through `foo`.
Once it's been through `foo` we can then unpack the state again with `restoreM`.
Hence we can apply `foo` to `bar` without losing track of the state.

Here `stM β = σ × β` is the 'packaged result state', but we can generalise:
if we have a tower `StateT σ₁ <| StateT σ₂ <| IO`, then we can get the
composite packaged state is going to be `stM₁₂ β := σ₁ × σ₂ × β` or `stM₁₂ := stM₁ ∘ stM₂`.

Now we can define `MonadControl m n`. Call `m` the 'base monad', in the above example it was `IO`.
`MonadControl m n` means that we can lift a monad function `foo : m α → m α` in the base monad
to a function `foo' : n α → n α` in the `n` monad, without having to manually handle the state of `n`.
Futhermore, `MonadControl` is transitive, which is what `MonadControlT` is, it's the transitive closure of `MonadControl`.

This is really useful when we have large towers of monad transformers, as we do in the metaprogramming library.

For example there is a function `withNewMCtxDepthImp : MetaM α → MetaM α` that runs the input monad instance
in a new nested metavariable context. We can lift this to `withNewMctxDepth : n α → n α` using `MonadControlT MetaM n`.
Which means that we can also run `withNewMctxDepth` in the `Tactic` monad without needing to
faff around with lifts and all the other boilerplate needed in `mapped_foo`.

-/

/-- MonadControl is a way of stating that the monad `m` can be 'run inside' the monad `n`.

This is the same as [`MonadBaseControl`](https://hackage.haskell.org/package/monad-control-1.0.3.1/docs/Control-Monad-Trans-Control.html#t:MonadBaseControl) in Haskell.
See the comment above this docstring for an explanation of how to use MonadControl.

-/
class MonadControl (m : Type u → Type v) (n : Type u → Type w) where
  stM      : Type u → Type u
  liftWith : {α : Type u} → (({β : Type u} → n β → m (stM β)) → m α) → n α
  restoreM : {α : Type u} → m (stM α) → n α

/-- Transitive closure of MonadControl. -/
class MonadControlT (m : Type u → Type v) (n : Type u → Type w) where
  stM      : Type u → Type u
  liftWith : {α : Type u} → (({β : Type u} → n β → m (stM β)) → m α) → n α
  restoreM {α : Type u} : stM α → n α

export MonadControlT (stM liftWith restoreM)

instance (m n o) [MonadControl n o] [MonadControlT m n] : MonadControlT m o where
  stM α := stM m n (MonadControl.stM n o α)
  liftWith f := MonadControl.liftWith fun x₂ => liftWith fun x₁ => f (x₁ ∘ x₂)
  restoreM := MonadControl.restoreM ∘ restoreM

instance (m : Type u → Type v) [Pure m] : MonadControlT m m where
  stM α := α
  liftWith f := f fun x => x
  restoreM x := pure x

@[inline]
def controlAt (m : Type u → Type v) {n : Type u → Type w} [s1 : MonadControlT m n] [s2 : Bind n] {α : Type u}
    (f : ({β : Type u} → n β → m (stM m n β)) → m (stM m n α)) : n α :=
  liftWith f >>= restoreM

@[inline]
def control {m : Type u → Type v} {n : Type u → Type w} [MonadControlT m n] [Bind n] {α : Type u}
    (f : ({β : Type u} → n β → m (stM m n β)) → m (stM m n α)) : n α :=
  controlAt m f

/-
  Typeclass for the polymorphic `forM` operation described in the "do unchained" paper.
  Remark:
  - `γ` is a "container" type of elements of type `α`.
  - `α` is treated as an output parameter by the typeclass resolution procedure.
    That is, it tries to find an instance using only `m` and `γ`.
-/
class ForM (m : Type u → Type v) (γ : Type w₁) (α : outParam (Type w₂)) where
  forM [Monad m] : γ → (α → m PUnit) → m PUnit

export ForM (forM)

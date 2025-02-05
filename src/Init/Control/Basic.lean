/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura, Sebastian Ullrich
-/
prelude
import Init.Core

universe u v w

/--
A `ForIn'` instance, which handles `for h : x in c do`,
can also handle `for x in x do` by ignoring `h`, and so provides a `ForIn` instance.

Note that this instance will cause a potentially non-defeq duplication if both `ForIn` and `ForIn'`
instances are provided for the same type.
-/
-- We set the priority to 500 so it is below the default,
-- but still above the low priority instance from `Stream`.
instance (priority := 500) instForInOfForIn' [ForIn' m ρ α d] : ForIn m ρ α where
  forIn x b f := forIn' x b fun a _ => f a

@[simp] theorem forIn'_eq_forIn [d : Membership α ρ] [ForIn' m ρ α d] {β} [Monad m] (x : ρ) (b : β)
    (f : (a : α) → a ∈ x → β → m (ForInStep β)) (g : (a : α) → β → m (ForInStep β))
    (h : ∀ a m b, f a m b = g a b) :
    forIn' x b f = forIn x b g := by
  simp [instForInOfForIn']
  congr
  apply funext
  intro a
  apply funext
  intro m
  apply funext
  intro b
  simp [h]
  rfl

/-- Extract the value from a `ForInStep`, ignoring whether it is `done` or `yield`. -/
def ForInStep.value (x : ForInStep α) : α :=
  match x with
  | ForInStep.done b => b
  | ForInStep.yield b => b

@[simp] theorem ForInStep.value_done (b : β) : (ForInStep.done b).value = b := rfl
@[simp] theorem ForInStep.value_yield (b : β) : (ForInStep.yield b).value = b := rfl

@[reducible]
def Functor.mapRev {f : Type u → Type v} [Functor f] {α β : Type u} : f α → (α → β) → f β :=
  fun a f => f <$> a

infixr:100 " <&> " => Functor.mapRev

recommended_spelling "mapRev" for "<&>" in [Functor.mapRev, «term_<&>_»]

@[always_inline, inline]
def Functor.discard {f : Type u → Type v} {α : Type u} [Functor f] (x : f α) : f PUnit :=
  Functor.mapConst PUnit.unit x

export Functor (discard)

/--
An `Alternative` functor is an `Applicative` functor that can "fail" or be "empty"
and a binary operation `<|>` that “collects values” or finds the “left-most success”.

Important instances include
* `Option`, where `failure := none` and `<|>` returns the left-most `some`.
* Parser combinators typically provide an `Applicative` instance for error-handling and
  backtracking.

Error recovery and state can interact subtly. For example, the implementation of `Alternative` for `OptionT (StateT σ Id)` keeps modifications made to the state while recovering from failure, while `StateT σ (OptionT Id)` discards them.
-/
-- NB: List instance is in mathlib. Once upstreamed, add
-- * `List`, where `failure` is the empty list and `<|>` concatenates.
class Alternative (f : Type u → Type v) extends Applicative f : Type (max (u+1) v) where
  /--
  Produces an empty collection or recoverable failure.  The `<|>` operator collects values or recovers
  from failures. See `Alternative` for more details.
  -/
  failure : {α : Type u} → f α
  /--
  Depending on the `Alternative` instance, collects values or recovers from `failure`s by
  returning the leftmost success. Can be written using the `<|>` operator syntax.
  -/
  orElse  : {α : Type u} → f α → (Unit → f α) → f α

instance (f : Type u → Type v) (α : Type u) [Alternative f] : OrElse (f α) := ⟨Alternative.orElse⟩

variable {f : Type u → Type v} [Alternative f] {α : Type u}

export Alternative (failure)

/--
If the proposition `p` is true, does nothing, else fails (using `failure`).
-/
@[always_inline, inline] def guard {f : Type → Type v} [Alternative f] (p : Prop) [Decidable p] : f Unit :=
  if p then pure () else failure

/--
Returns `some x` if `f` succeeds with value `x`, else returns `none`.
-/
@[always_inline, inline] def optional (x : f α) : f (Option α) :=
  some <$> x <|> pure none

class ToBool (α : Type u) where
  toBool : α → Bool

export ToBool (toBool)

instance : ToBool Bool where
  toBool b := b

@[macro_inline] def bool {β : Type u} {α : Type v} [ToBool β] (f t : α) (b : β) : α :=
  match toBool b with
  | true  => t
  | false => f

@[macro_inline] def orM {m : Type u → Type v} {β : Type u} [Monad m] [ToBool β] (x y : m β) : m β := do
  let b ← x
  match toBool b with
  | true  => pure b
  | false => y

infixr:30 " <||> " => orM

recommended_spelling "orM" for "<||>" in [orM, «term_<||>_»]

@[macro_inline] def andM {m : Type u → Type v} {β : Type u} [Monad m] [ToBool β] (x y : m β) : m β := do
  let b ← x
  match toBool b with
  | true  => y
  | false => pure b

infixr:35 " <&&> " => andM

recommended_spelling "andM" for "<&&>" in [andM, «term_<&&>_»]

@[macro_inline] def notM {m : Type → Type v} [Applicative m] (x : m Bool) : m Bool :=
  not <$> x

/-!
# How `MonadControl` works

There is a [tutorial by Alexis King](https://lexi-lambda.github.io/blog/2019/09/07/demystifying-monadbasecontrol/) that this docstring is based on.

Suppose we have `foo : ∀ α, IO α → IO α` and `bar : StateT σ IO β` (ie, `bar : σ → IO (σ × β)`).
We might want to 'map' `bar` by `foo`. Concretely we would write this as:

```lean
opaque foo : ∀ {α}, IO α → IO α
opaque bar : StateT σ IO β

def mapped_foo : StateT σ IO β := do
  let s ← get
  let (b, s') ← liftM <| foo <| StateT.run bar s
  set s'
  return b
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
- Define `restoreM : IO (stM α) → StateT σ IO α` as below

```lean
def stM (α : Type) := α × σ

def restoreM (x : IO (stM α)) : StateT σ IO α := do
  let (a,s) ← liftM x
  set s
  return a
```

To get:

```lean
def mapped_foo' : StateT σ IO β := do
  let s ← get
  let mapInBase := fun z => StateT.run z s
  restoreM <| foo <| mapInBase bar
```

and finally define

```lean
def control {α : Type}
  (f : ({β : Type} → StateT σ IO β → IO (stM β)) → IO (stM α))
  : StateT σ IO α := do
  let s ← get
  let mapInBase := fun {β} (z : StateT σ IO β) => StateT.run z s
  let r : IO (stM α) := f mapInBase
  restoreM r
```

Now we can write `mapped_foo` as:

```lean
def mapped_foo'' : StateT σ IO β :=
  control (fun mapInBase => foo (mapInBase bar))
```

The core idea of `mapInBase` is that given any `β`, it runs an instance of
`StateT σ IO β` and 'packages' the result and state as  `IO (stM β)` so that it can be piped through `foo`.
Once it's been through `foo` we can then unpack the state again with `restoreM`.
Hence we can apply `foo` to `bar` without losing track of the state.

Here `stM β = σ × β` is the 'packaged result state', but we can generalise:
if we have a tower `StateT σ₁ <| StateT σ₂ <| IO`, then the
composite packaged state is going to be `stM₁₂ β := σ₁ × σ₂ × β` or `stM₁₂ := stM₁ ∘ stM₂`.

`MonadControl m n` means that when programming in the monad `n`,
we can switch to a base monad `m` using `control`, just like with `liftM`.
In contrast to `liftM`, however, we also get a function `runInBase` that
allows us to "lower" actions in `n` into `m`.
This is really useful when we have large towers of monad transformers, as we do in the metaprogramming library.

For example there is a function `withNewMCtxDepthImp : MetaM α → MetaM α` that runs the input monad instance
in a new nested metavariable context. We can lift this to `withNewMctxDepth : n α → n α` using `MonadControlT MetaM n`
(`MonadControlT` is the transitive closure of `MonadControl`).
Which means that we can also run `withNewMctxDepth` in the `Tactic` monad without needing to
faff around with lifts and all the other boilerplate needed in `mapped_foo`.

## Relationship to `MonadFunctor`

A stricter form of `MonadControl` is `MonadFunctor`, which defines
`monadMap {α} : (∀ {β}, m β → m β) → n α → n α`. Using `monadMap` it is also possible to define `mapped_foo` above.
However there are some mappings which can't be derived using `MonadFunctor`. For example:

```lean,ignore
 @[inline] def map1MetaM [MonadControlT MetaM n] [Monad n] (f : forall {α}, (β → MetaM α) → MetaM α) {α} (k : β → n α) : n α :=
   control fun runInBase => f fun b => runInBase <| k b

 @[inline] def map2MetaM [MonadControlT MetaM n] [Monad n] (f : forall {α}, (β → γ → MetaM α) → MetaM α) {α} (k : β → γ → n α) : n α :=
   control fun runInBase => f fun b c => runInBase <| k b c
```

In `monadMap`, we can only 'run in base' a single computation in `n` into the base monad `m`.
Using `control` means that `runInBase` can be used multiple times.

-/


/-- MonadControl is a way of stating that the monad `m` can be 'run inside' the monad `n`.

This is the same as [`MonadBaseControl`](https://hackage.haskell.org/package/monad-control-1.0.3.1/docs/Control-Monad-Trans-Control.html#t:MonadBaseControl) in Haskell.
To learn about `MonadControl`, see the comment above this docstring.

-/
class MonadControl (m : semiOutParam (Type u → Type v)) (n : Type u → Type w) where
  stM      : Type u → Type u
  liftWith : {α : Type u} → (({β : Type u} → n β → m (stM β)) → m α) → n α
  restoreM : {α : Type u} → m (stM α) → n α

/-- Transitive closure of MonadControl. -/
class MonadControlT (m : Type u → Type v) (n : Type u → Type w) where
  stM      : Type u → Type u
  liftWith : {α : Type u} → (({β : Type u} → n β → m (stM β)) → m α) → n α
  restoreM {α : Type u} : m (stM α) → n α

export MonadControlT (stM liftWith restoreM)

@[always_inline]
instance (m n o) [MonadControl n o] [MonadControlT m n] : MonadControlT m o where
  stM α := stM m n (MonadControl.stM n o α)
  liftWith f := MonadControl.liftWith fun x₂ => liftWith fun x₁ => f (x₁ ∘ x₂)
  restoreM := MonadControl.restoreM ∘ restoreM

instance (m : Type u → Type v) : MonadControlT m m where
  stM α := α
  liftWith f := f fun x => x
  restoreM x := x

@[always_inline, inline]
def controlAt (m : Type u → Type v) {n : Type u → Type w} [MonadControlT m n] [Pure m] [Bind n]
    {α : Type u} (f : ({β : Type u} → n β → m (stM m n β)) → m (stM m n α)) : n α :=
  liftWith f >>= restoreM ∘ pure

@[always_inline, inline]
def control {m : Type u → Type v} {n : Type u → Type w} [MonadControlT m n] [Pure m] [Bind n]
    {α : Type u} (f : ({β : Type u} → n β → m (stM m n β)) → m (stM m n α)) : n α :=
  controlAt m f

/--
  Typeclass for the polymorphic `forM` operation described in the "do unchained" paper.
  Remark:
  - `γ` is a "container" type of elements of type `α`.
  - `α` is treated as an output parameter by the typeclass resolution procedure.
    That is, it tries to find an instance using only `m` and `γ`.
-/
class ForM (m : Type u → Type v) (γ : Type w₁) (α : outParam (Type w₂)) where
  forM [Monad m] : γ → (α → m PUnit) → m PUnit

export ForM (forM)

/-- Left-to-right composition of Kleisli arrows. -/
@[always_inline]
def Bind.kleisliRight [Bind m] (f₁ : α → m β) (f₂ : β → m γ) (a : α) : m γ :=
  f₁ a >>= f₂

/-- Right-to-left composition of Kleisli arrows. -/
@[always_inline]
def Bind.kleisliLeft [Bind m] (f₂ : β → m γ) (f₁ : α → m β) (a : α) : m γ :=
  f₁ a >>= f₂

/-- Same as `Bind.bind` but with arguments swapped. -/
@[always_inline]
def Bind.bindLeft [Bind m] (f : α → m β) (ma : m α) : m β :=
  ma >>= f

-- Precedence choice taken to be the same as in haskell:
-- https://hackage.haskell.org/package/base-4.17.0.0/docs/Control-Monad.html#v:-61--60--60-
@[inherit_doc] infixr:55 " >=> " => Bind.kleisliRight
@[inherit_doc] infixr:55 " <=< " => Bind.kleisliLeft
@[inherit_doc] infixr:55 " =<< " => Bind.bindLeft

recommended_spelling "kleisliRight" for ">=>" in [Bind.kleisliRight, «term_>=>_»]
recommended_spelling "kleisliLeft" for "<=<" in [Bind.kleisliLeft, «term_<=<_»]
recommended_spelling "bindLeft" for "=<<" in [Bind.bindLeft, «term_=<<_»]

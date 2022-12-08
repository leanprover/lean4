/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro
-/
prelude
import Init.Prelude
set_option linter.missingDocs true -- keep it documented

/-!
# Coercion

Lean uses a somewhat elaborate system of typeclasses to drive the coercion system.
Here a *coercion* means an invisible function that is automatically inserted
to fix what would otherwise be a type error. For example, if we have:
```
def f (x : Nat) : Int := x
```
then this is clearly not type correct as is, because `x` has type `Nat` but
type `Int` is expected, and normally you will get an error message saying exactly that.
But before it shows that message, it will attempt to synthesize an instance of
`CoeT Nat x Int`, which will end up going through all the other typeclasses defined
below, to discover that there is an instance of `Coe Nat Int` defined.

This instance is defined as:
```
instance : Coe Nat Int := ⟨Int.ofNat⟩
```
so Lean will elaborate the original function `f` as if it said:
```
def f (x : Nat) : Int := Int.ofNat x
```
which is not a type error anymore.

You can also use the `↑` operator to explicitly indicate a coercion. Using `↑x`
instead of `x` in the example will result in the same output.
Because there are many polymorphic functions in Lean, it is often ambiguous where
the coercion can go. For example:
```
def f (x y : Nat) : Int := x + y
```
This could be either `↑x + ↑y` where `+` is the addition on `Int`, or `↑(x + y)`
where `+` is addition on `Nat`, or even `x + y` using a heterogeneous addition
with the type `Nat → Nat → Int`. You can use the `↑` operator to disambiguate
between these possibilities, but generally Lean will elaborate working from the
"outside in", meaning that it will first look at the expression `_ + _ : Int`
and assign the `+` to be the one for `Int`, and then need to insert coercions
for the subterms `↑x : Int` and `↑y : Int`, resulting in the `↑x + ↑y` version.

## Important typeclasses

* `Coe α β` is the most basic class, and the usual one you will want to use
  when implementing a coercion for your own types.

* `CoeDep α (x : α) β` allows `β` to depend not only on `α` but on the value
  `x : α` itself. This is useful when the coercion function is dependent.
  An example of a dependent coercion is the instance for `Prop → Bool`, because
  it only holds for `Decidable` propositions. It is defined as:
  ```
  instance (p : Prop) [Decidable p] : CoeDep Prop p Bool := ...
  ```

* `CoeFun α (γ : α → Sort v)` is a coercion to a function. `γ a` should be a
  (coercion-to-)function type, and this is triggered whenever an element
  `f : α` appears in an application like `f x` which would not make sense since
  `f` does not have a function type. This is automatically turned into `CoeFun.coe f x`.

* `CoeSort α β` is a coercion to a sort. `β` must be a universe, and if
  `a : α` appears in a place where a type is expected, like `(x : a)` or `a → a`,
  then it will be turned into `(x : CoeSort.coe a)`.

* `CoeHead` is like `Coe`, but while `Coe` can be transitively chained in the
  `CoeT` class, `CoeHead` can only appear once and only at the start of such a
  chain. This is useful when the transitive instances are not well behaved.

* `CoeTail` is similar: it can only appear at the end of a chain of coercions.

* `CoeT α (x : α) β` itself is the combination of all the aforementioned classes
  (except `CoeSort` and `CoeFun` which have different triggers). You can
  implement `CoeT` if you do not want this coercion to be transitively composed
  with any other coercions.

Note that unlike most operators like `+`, `↑` is always eagerly unfolded at
parse time into its definition. So if we look at the definition of `f` from
before, we see no trace of the `CoeT.coe` function:
```
def f (x : Nat) : Int := x
#print f
-- def f : Nat → Int :=
-- fun (x : Nat) => Int.ofNat x
```
-/

universe u v w w'

/--
`Coe α β` is the typeclass for coercions from `α` to `β`. It can be transitively
chained with other `Coe` instances, and coercion is automatically used when
`x` has type `α` but it is used in a context where `β` is expected.
You can use the `↑x` operator to explicitly trigger coercion.
-/
class Coe (α : Sort u) (β : Sort v) where
  /-- Coerces a value of type `α` to type `β`. Accessible by the notation `↑x`,
  or by double type ascription `((x : α) : β)`. -/
  coe : α → β

/--
Auxiliary class that contains the transitive closure of `Coe`.
Users should generally not implement this directly.
-/
class CoeTC (α : Sort u) (β : Sort v) where
  /-- Coerces a value of type `α` to type `β`. Accessible by the notation `↑x`,
  or by double type ascription `((x : α) : β)`. -/
  coe : α → β

/--
`CoeHead α β` is for coercions that can only appear at the beginning of a
sequence of coercions. That is, `β` can be further coerced via `Coe β γ` and
`CoeTail γ δ` instances but `α` will only be the inferred type of the input.
-/
class CoeHead (α : Sort u) (β : Sort v) where
  /-- Coerces a value of type `α` to type `β`. Accessible by the notation `↑x`,
  or by double type ascription `((x : α) : β)`. -/
  coe : α → β

/--
`CoeTail α β` is for coercions that can only appear at the end of a
sequence of coercions. That is, `α` can be further coerced via `Coe σ α` and
`CoeHead τ σ` instances but `β` will only be the expected type of the expression.
-/
class CoeTail (α : Sort u) (β : Sort v) where
  /-- Coerces a value of type `α` to type `β`. Accessible by the notation `↑x`,
  or by double type ascription `((x : α) : β)`. -/
  coe : α → β

/--
Auxiliary class that contains `CoeHead` + `CoeTC` + `CoeTail`.

A `CoeHTCT` chain has the "grammar" `(CoeHead)? (Coe)* (CoeTail)?`, except that
the empty sequence is not allowed.
-/
class CoeHTCT (α : Sort u) (β : Sort v) where
  /-- Coerces a value of type `α` to type `β`. Accessible by the notation `↑x`,
  or by double type ascription `((x : α) : β)`. -/
  coe : α → β

/--
`CoeDep α (x : α) β` is a typeclass for dependent coercions, that is, the type `β`
can depend on `x` (or rather, the value of `x` is available to typeclass search
so an instance that relates `β` to `x` is allowed).

Dependent coercions do not participate in the transitive chaining process of
regular coercions: they must exactly match the type mismatch on both sides.
-/
class CoeDep (α : Sort u) (_ : α) (β : Sort v) where
  /-- The resulting value of type `β`. The input `x : α` is a parameter to
  the type class, so the value of type `β` may possibly depend on additional
  typeclasses on `x`. -/
  coe : β

/--
`CoeT` is the core typeclass which is invoked by Lean to resolve a type error.
It can also be triggered explicitly with the notation `↑x` or by double type
ascription `((x : α) : β)`.

A `CoeT` chain has the "grammar" `(CoeHead)? (Coe)* (CoeTail)? | CoeDep`,
except that the empty sequence is not allowed (identity coercions don't need
the coercion system at all).
-/
class CoeT (α : Sort u) (_ : α) (β : Sort v) where
  /-- The resulting value of type `β`. The input `x : α` is a parameter to
  the type class, so the value of type `β` may possibly depend on additional
  typeclasses on `x`. -/
  coe : β


/--
`CoeFun α (γ : α → Sort v)` is a coercion to a function. `γ a` should be a
(coercion-to-)function type, and this is triggered whenever an element
`f : α` appears in an application like `f x` which would not make sense since
`f` does not have a function type. This is automatically turned into `CoeFun.coe f x`.
-/
class CoeFun (α : Sort u) (γ : outParam (α → Sort v)) where
  /-- Coerces a value `f : α` to type `γ f`, which should be either be a
  function type or another `CoeFun` type, in order to resolve a mistyped
  application `f x`. -/
  coe : (f : α) → γ f

/--
`CoeSort α β` is a coercion to a sort. `β` must be a universe, and if
`a : α` appears in a place where a type is expected, like `(x : a)` or `a → a`,
then it will be turned into `(x : CoeSort.coe a)`.
-/
class CoeSort (α : Sort u) (β : outParam (Sort v)) where
  /-- Coerces a value of type `α` to `β`, which must be a universe. -/
  coe : α → β

/--
`↑x` represents a coercion, which converts `x` of type `α` to type `β`, using
typeclasses to resolve a suitable conversion function. You can often leave the
`↑` off entirely, since coercion is triggered implicitly whenever there is a
type error, but in ambiguous cases it can be useful to use `↑` to disambiguate
between e.g. `↑x + ↑y` and `↑(x + y)`.
-/
syntax:1024 (name := coeNotation) "↑" term:1024 : term

instance coeTrans {α : Sort u} {β : Sort v} {δ : Sort w} [Coe β δ] [CoeTC α β] : CoeTC α δ where
  coe a := Coe.coe (CoeTC.coe a : β)

instance coeBase {α : Sort u} {β : Sort v} [Coe α β] : CoeTC α β where
  coe a := Coe.coe a

instance coeOfHeafOfTCOfTail {α : Sort u} {β : Sort v} {δ : Sort w} {γ : Sort w'} [CoeHead α β] [CoeTail δ γ] [CoeTC β δ] : CoeHTCT α γ where
  coe a := CoeTail.coe (CoeTC.coe (CoeHead.coe a : β) : δ)

instance coeOfHeadOfTC {α : Sort u} {β : Sort v} {δ : Sort w} [CoeHead α β] [CoeTC β δ] : CoeHTCT α δ  where
  coe a := CoeTC.coe (CoeHead.coe a : β)

instance coeOfTCOfTail {α : Sort u} {β : Sort v} {δ : Sort w} [CoeTail β δ] [CoeTC α β] : CoeHTCT α δ where
  coe a := CoeTail.coe (CoeTC.coe a : β)

instance coeOfHeadOfTail {α : Sort u} {β : Sort v} {γ : Sort w} [CoeHead α β] [CoeTail β γ] : CoeHTCT α γ where
  coe a := CoeTail.coe (CoeHead.coe a : β)

instance coeOfHead {α : Sort u} {β : Sort v} [CoeHead α β] : CoeHTCT α β where
  coe a := CoeHead.coe a

instance coeOfTail {α : Sort u} {β : Sort v} [CoeTail α β] : CoeHTCT α β where
  coe a := CoeTail.coe a

instance coeOfTC {α : Sort u} {β : Sort v} [CoeTC α β] : CoeHTCT α β where
  coe a := CoeTC.coe a

instance coeOfHTCT {α : Sort u} {β : Sort v} [CoeHTCT α β] (a : α) : CoeT α a β where
  coe := CoeHTCT.coe a

instance coeOfDep {α : Sort u} {β : Sort v} (a : α) [CoeDep α a β] : CoeT α a β where
  coe := CoeDep.coe a

instance coeId {α : Sort u} (a : α) : CoeT α a α where
  coe := a

instance coeSortToCoeTail [inst : CoeSort α β] : CoeTail α β where
  coe := inst.coe

/-! # Basic instances -/

instance boolToProp : Coe Bool Prop where
  coe b := Eq b true

instance boolToSort : CoeSort Bool Prop where
  coe b := Eq b true

instance decPropToBool (p : Prop) [Decidable p] : CoeDep Prop p Bool where
  coe := decide p

instance optionCoe {α : Type u} : CoeTail α (Option α) where
  coe := some

instance subtypeCoe {α : Sort u} {p : α → Prop} : CoeHead (Subtype p) α where
  coe v := v.val

/-! # Coe bridge -/

/--
Helper definition used by the elaborator. It is not meant to be used directly by users.

This is used for coercions between monads, in the case where we want to apply
a monad lift and a coercion on the result type at the same time.
-/
@[inline] def Lean.Internal.liftCoeM {m : Type u → Type v} {n : Type u → Type w} {α β : Type u}
    [MonadLiftT m n] [∀ a, CoeT α a β] [Monad n] (x : m α) : n β := do
  let a ← liftM x
  pure (CoeT.coe a)

/--
Helper definition used by the elaborator. It is not meant to be used directly by users.

This is used for coercing the result type under a monad.
-/
@[inline] def Lean.Internal.coeM {m : Type u → Type v} {α β : Type u}
    [∀ a, CoeT α a β] [Monad m] (x : m α) : m β := do
  let a ← x
  pure (CoeT.coe a)

instance [CoeFun α β] (a : α) : CoeDep α a (β a) where
  coe := CoeFun.coe a

instance [CoeFun α (fun _ => β)] : CoeTail α β  where
  coe a := CoeFun.coe a

instance [CoeSort α β] : CoeTail α β where
  coe a := CoeSort.coe a

/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro
-/
prelude
import Init.Control.Basic

namespace Option

deriving instance DecidableEq for Option
deriving instance BEq for Option

/-- Lifts an optional value to any `Alternative`, sending `none` to `failure`. -/
def getM [Alternative m] : Option α → m α
  | none     => failure
  | some a   => pure a

/-- Returns `true` on `some x` and `false` on `none`. -/
@[inline] def isSome : Option α → Bool
  | some _ => true
  | none   => false

@[simp] theorem isSome_none : @isSome α none = false := rfl
@[simp] theorem isSome_some : isSome (some a) = true := rfl

/--
Returns `true` on `none` and `false` on `some x`.

This function is more flexible than `(· == none)` because it does not require a `BEq α` instance.

Examples:
 * `(none : Option Nat).isNone = true`
 * `(some Nat.add).isNone = false`
-/
@[inline] def isNone : Option α → Bool
  | some _ => false
  | none   => true

@[simp] theorem isNone_none : @isNone α none = true := rfl
@[simp] theorem isNone_some : isNone (some a) = false := rfl

/--
Checks whether an optional value is both present and equal to some other value.

Given `x? : Option α` and `y : α`, `x?.isEqSome y` is equivalent to `x? == some y`. It is more
efficient because it avoids an allocation.
-/
@[inline] def isEqSome [BEq α] : Option α → α → Bool
  | some a, b => a == b
  | none,   _ => false

/--
Sequencing of `Option` computations.

From the perspective of `Option` as computations that might fail, this function sequences
potentially-failing computations, failing if either fails. From the perspective of `Option` as a
collection with at most one element, the function is applied to the element if present, and the
final result is empty if either the initial or the resulting collections are empty.

This function is often accessed via the `>>=` operator from the `Bind (Option α)` instance, or
implicitly via `do`-notation, but it is also idiomatic to call it using [generalized field
notation](lean-manual://section/generalized-field-notation).

Examples:
 * `none.bind (fun x => some x) = none`
 * `(some 4).bind (fun x => some x) = some 4`
 * `none.bind (Option.guard (· > 2)) = none`
 * `(some 2).bind (Option.guard (· > 2)) = none`
 * `(some 4).bind (Option.guard (· > 2)) = some 4`
-/
@[inline] protected def bind : Option α → (α → Option β) → Option β
  | none,   _ => none
  | some a, f => f a

/--
Runs the monadic action `f` on `o`'s value, if any, and returns the result, or  `none` if there is
no value.

From the perspective of `Option` as a collection with at most one element, the monadic the function
is applied to the element if present, and the final result is empty if either the initial or the
resulting collections are empty.
-/
@[inline] protected def bindM [Monad m] (f : α → m (Option β)) (o : Option α) : m (Option β) := do
  if let some a := o then
    return (← f a)
  else
    return none

/--
Runs a monadic function `f` on an optional value, returning the result. If the optional value is
`none`, the function is not called and the result is also `none`.

From the perspective of `Option` as a container with at most one element, this is analogous to
`List.mapM`, returning the result of running the monadic function on all elements of the container.

`Option.mapA` is the corresponding operation for applicative functors.
-/
@[inline] protected def mapM [Monad m] (f : α → m β) (o : Option α) : m (Option β) := do
  if let some a := o then
    return some (← f a)
  else
    return none

theorem map_id : (Option.map id : Option α → Option α) = id :=
  funext (fun o => match o with | none => rfl | some _ => rfl)

/--
Keeps an optional value only if it satisfies a Boolean predicate.

If `Option` is thought of as a collection that contains at most one element, then `Option.filter` is
analogous to `List.filter` or `Array.filter`.

Examples:
 * `(some 5).filter (· % 2 == 0) = none`
 * `(some 4).filter (· % 2 == 0) = some 4`
 * `none.filter (fun x : Nat => x % 2 == 0) = none`
 * `none.filter (fun x : Nat => true) = none`
-/
@[always_inline, inline] protected def filter (p : α → Bool) : Option α → Option α
  | some a => if p a then some a else none
  | none   => none

/--
Checks whether an optional value either satisfies a Boolean predicate or is `none`.

Examples:
 * `(some 33).all (· % 2 == 0) = false
 * `(some 22).all (· % 2 == 0) = true
 * `none.all (fun x : Nat => x % 2 == 0) = true
-/
@[always_inline, inline] protected def all (p : α → Bool) : Option α → Bool
  | some a => p a
  | none   => true

/--
Checks whether an optional value is not `none` and satisfies a Boolean predicate.

Examples:
 * `(some 33).any (· % 2 == 0) = false
 * `(some 22).any (· % 2 == 0) = true
 * `none.any (fun x : Nat => true) = false
-/
@[always_inline, inline] protected def any (p : α → Bool) : Option α → Bool
  | some a => p a
  | none   => false

/--
Implementation of `OrElse`'s `<|>` syntax for `Option`. If the first argument is `some a`, returns
`some a`, otherwise evaluates and returns the second argument.

See also `or` for a version that is strict in the second argument.
-/
@[always_inline, macro_inline] protected def orElse : Option α → (Unit → Option α) → Option α
  | some a, _ => some a
  | none,   b => b ()

instance : OrElse (Option α) where
  orElse := Option.orElse

/--
Returns the first of its arguments that is `some`, or `none` if neither is `some`.

This is similar to the `<|>` operator, also known as `OrElse.orElse`, but both arguments are always
evaluated without short-circuiting.
-/
@[always_inline, macro_inline] def or : Option α → Option α → Option α
  | some a, _ => some a
  | none,   b => b

/--
Lifts an ordering relation to `Option`, such that `none` is the least element.

It can be understood as adding a distinguished least element, represented by `none`, to both `α` and
`β`.

This definition is part of the implementation of the `LT (Option α)` instance. However, because it
can be used with heterogeneous relations, it is sometimes useful on its own.

Examples:
 * `Option.lt (fun n k : Nat => n < k) none none = False`
 * `Option.lt (fun n k : Nat => n < k) none (some 3) = True`
 * `Option.lt (fun n k : Nat => n < k) (some 3) none = False`
 * `Option.lt (fun n k : Nat => n < k) (some 4) (some 5) = True`
 * `Option.lt (fun n k : Nat => n < k) (some 4) (some 4) = False`
-/
@[inline] protected def lt (r : α → β → Prop) : Option α → Option β → Prop
  | none,   some _ => True
  | some x, some y => r x y
  | _,      _      => False

@[inline] protected def le (r : α → β → Prop) : Option α → Option β → Prop
  | none,   some _ => True
  | none,   none   => True
  | some _, none   => False
  | some x, some y => r x y

instance (r : α → β → Prop) [s : DecidableRel r] : DecidableRel (Option.lt r)
  | none,   some _ => isTrue  trivial
  | some x, some y => s x y
  | some _, none   => isFalse not_false
  | none,   none   => isFalse not_false

/--
Applies a function to a two optional values if both are present. Otherwise, if one value is present,
it is returned and the function is not used.

The value is `some (fn a b)` if the inputs are `some a` and `some b`. Otherwise, the behavior is
equivalent to `Option.orElse`: if only one input is `some x`, then the value is `some x`, and if
both are `none`, then the value is `none`.

Examples:
 * `Option.zipWith (· + ·) none (some 3) = some 3`
 * `Option.zipWith (· + ·) (some 2) (some 3) = some 5`
 * `Option.zipWith (· + ·) (some 2) none = some 2`
 * `Option.zipWith (· + ·) none none = none`
-/
def zipWith (fn : α → α → α) : Option α → Option α → Option α
  | none  , none   => none
  | some x, none   => some x
  | none  , some y => some y
  | some x, some y => some <| fn x y

/--
Applies a function to a two optional values if both are present. Otherwise, if one value is present,
it is returned and the function is not used.

The value is `some (fn a b)` if the inputs are `some a` and `some b`. Otherwise, the behavior is
equivalent to `Option.orElse`: if only one input is `some x`, then the value is `some x`, and if
both are `none`, then the value is `none`.

Examples:
 * `Option.merge (· + ·) none (some 3) = some 3`
 * `Option.merge (· + ·) (some 2) (some 3) = some 5`
 * `Option.merge (· + ·) (some 2) none = some 2`
 * `Option.merge (· + ·) none none = none`
-/
@[deprecated zipWith (since := "2025-04-04")]
def merge (fn : α → α → α) : Option α → Option α → Option α
  | none  , none   => none
  | some x, none   => some x
  | none  , some y => some y
  | some x, some y => some <| fn x y

@[simp] theorem getD_none : getD none a = a := rfl
@[simp] theorem getD_some : getD (some a) b = a := rfl

@[simp] theorem map_none' (f : α → β) : none.map f = none := rfl
@[simp] theorem map_some' (a) (f : α → β) : (some a).map f = some (f a) := rfl

@[simp] theorem none_bind (f : α → Option β) : none.bind f = none := rfl
@[simp] theorem some_bind (a) (f : α → Option β) : (some a).bind f = f a := rfl


/--
A case analysis function for `Option`.

Given a value for `none` and a function to apply to the contents of `some`, `Option.elim` checks
which constructor a given `Option` consists of, and uses the appropriate argument.

`Option.elim` is an elimination principle for `Option`. In particular, it is a non-dependent version
of `Option.recOn`. It can also be seen as a combination of `Option.map` and `Option.getD`.

Examples:
 * `(some "hello").elim 0 String.length = 5`
 * `none.elim 0 String.length = 0`
-/
@[inline] protected def elim : Option α → β → (α → β) → β
  | some x, _, f => f x
  | none, y, _ => y

/--
Extracts the value from an option that can be proven to be `some`.
-/
@[inline] def get {α : Type u} : (o : Option α) → isSome o → α
  | some x, _ => x

@[simp] theorem some_get : ∀ {x : Option α} (h : isSome x), some (x.get h) = x
| some _, _ => rfl
@[simp] theorem get_some (x : α) (h : isSome (some x)) : (some x).get h = x := rfl

/--
Returns `none` if a value doesn't satisfy a predicate, or the value itself otherwise.

From the perspective of `Option` as computations that might fail, this function is a run-time
assertion operator in the `Option` monad.

Examples:
 * `Option.guard (· > 2) 1 = none`
 * `Option.guard (· > 2) 5 = some 5`
-/
@[inline] def guard (p : α → Prop) [DecidablePred p] (a : α) : Option α :=
  if p a then some a else none

/--
Converts an optional value to a list with zero or one element.

Examples:
 * `(some "value").toList = ["value"]`
 * `none.toList = []`
-/
@[inline] def toList : Option α → List α
  | none => .nil
  | some a => .cons a .nil

/--
Converts an optional value to an array with zero or one element.

Examples:
 * `(some "value").toArray = #["value"]`
 * `none.toArray = #[]`
-/
@[inline] def toArray : Option α → Array α
  | none => List.toArray .nil
  | some a => List.toArray (.cons a .nil)

/--
Applies a function to a two optional values if both are present. Otherwise, if one value is present,
it is returned and the function is not used.

The value is `some (f a b)` if the inputs are `some a` and `some b`. Otherwise, the behavior is
equivalent to `Option.orElse`. If only one input is `some x`, then the value is `some x`. If both
are `none`, then the value is `none`.

Examples:
 * `Option.liftOrGet (· + ·) none (some 3) = some 3`
 * `Option.liftOrGet (· + ·) (some 2) (some 3) = some 5`
 * `Option.liftOrGet (· + ·) (some 2) none = some 2`
 * `Option.liftOrGet (· + ·) none none = none`
-/
@[deprecated zipWith (since := "2025-04-04")]
def liftOrGet (f : α → α → α) : Option α → Option α → Option α
  | none, none => none
  | some a, none => some a
  | none, some b => some b
  | some a, some b => some (f a b)

/-- Lifts a relation `α → β → Prop` to a relation `Option α → Option β → Prop` by just adding
`none ~ none`. -/
inductive Rel (r : α → β → Prop) : Option α → Option β → Prop
  /-- If `a ~ b`, then `some a ~ some b` -/
  | some {a b} : r a b → Rel r (some a) (some b)
  /-- `none ~ none` -/
  | none : Rel r none none

/--
Flattens nested optional values, preserving any value found.

This is analogous to `List.flatten`.

Examples:
 * `none.join = none`
 * `(some none).join = none`
 * `(some (some v)).join = some v`
-/
@[simp, inline] def join (x : Option (Option α)) : Option α := x.bind id

/--
Applies a function in some applicative functor to an optional value, returning `none` with no
effects if the value is missing.

This is analogous to `Option.mapM` for monads.
-/
@[inline] protected def mapA [Applicative m] {α β} (f : α → m β) : Option α → m (Option β)
  | none => pure none
  | some x => some <$> f x

/--
Converts an optional monadic computation into a monadic computation of an optional value.

Example:
```lean example
#eval show IO (Option String) from
  Option.sequence <| some do
    IO.println "hello"
    return "world"
```
```output
hello
```
```output
some "world"
```
-/
@[inline] def sequence [Monad m] {α : Type u} : Option (m α) → m (Option α)
  | none => pure none
  | some fn => some <$> fn


/--
A monadic case analysis function for `Option`.

Given a fallback computation for `none` and a monadic operation to apply to the contents of `some`,
`Option.elimM` checks which constructor a given `Option` consists of, and uses the appropriate
argument.

`Option.elimM` can also be seen as a combination of `Option.mapM` and `Option.getDM`. It is a
monadic analogue of `Option.elim`.
-/
@[inline] def elimM [Monad m] (x : m (Option α)) (y : m β) (z : α → m β) : m β :=
  do (← x).elim y z

/--
Gets the value in an option, monadically computing a default value on `none`.

This is the monadic analogue of `Option.getD`.
-/

@[inline] def getDM [Monad m] (x : Option α) (y : m α) : m α :=
  match x with
  | some a => pure a
  | none => y

instance (α) [BEq α] [LawfulBEq α] : LawfulBEq (Option α) where
  rfl {x} :=
    match x with
    | some _ => LawfulBEq.rfl (α := α)
    | none => rfl
  eq_of_beq {x y h} := by
    match x, y with
    | some x, some y => rw [LawfulBEq.eq_of_beq (α := α) h]
    | none, none => rfl

@[simp] theorem all_none : Option.all p none = true := rfl
@[simp] theorem all_some : Option.all p (some x) = p x := rfl

@[simp] theorem any_none : Option.any p none = false := rfl
@[simp] theorem any_some : Option.any p (some x) = p x := rfl

/--
The minimum of two optional values, with `none` treated as the least element. This function is
usually accessed through the `Min (Option α)` instance, rather than directly.

Prior to `nightly-2025-02-27`, `none` was treated as the greatest element, so
`min none (some x) = min (some x) none = some x`.

Examples:
 * `Option.min (some 2) (some 5) = some 2`
 * `Option.min (some 5) (some 2) = some 2`
 * `Option.min (some 2) none = none`
 * `Option.min none (some 5) = none`
 * `Option.min none none = none`
-/
protected def min [Min α] : Option α → Option α → Option α
  | some x, some y => some (Min.min x y)
  | some _, none => none
  | none, some _ => none
  | none, none => none

instance [Min α] : Min (Option α) where min := Option.min

@[simp] theorem min_some_some [Min α] {a b : α} : min (some a) (some b) = some (min a b) := rfl
@[simp] theorem min_some_none [Min α] {a : α} : min (some a) none = none := rfl
@[simp] theorem min_none_some [Min α] {b : α} : min none (some b) = none := rfl
@[simp] theorem min_none_none [Min α] : min (none : Option α) none = none := rfl

/--
The maximum of two optional values.

This function is usually accessed through the `Max (Option α)` instance, rather than directly.

Examples:
 * `Option.max (some 2) (some 5) = some 5`
 * `Option.max (some 5) (some 2) = some 5`
 * `Option.max (some 2) none = some 2`
 * `Option.max none (some 5) = some 5`
 * `Option.max none none = none`
-/
protected def max [Max α] : Option α → Option α → Option α
  | some x, some y => some (Max.max x y)
  | some x, none => some x
  | none, some y => some y
  | none, none => none

instance [Max α] : Max (Option α) where max := Option.max

@[simp] theorem max_some_some [Max α] {a b : α} : max (some a) (some b) = some (max a b) := rfl
@[simp] theorem max_some_none [Max α] {a : α} : max (some a) none = some a := rfl
@[simp] theorem max_none_some [Max α] {b : α} : max none (some b) = some b := rfl
@[simp] theorem max_none_none [Max α] : max (none : Option α) none = none := rfl


end Option

instance [LT α] : LT (Option α) where
  lt := Option.lt (· < ·)

instance [LE α] : LE (Option α) where
  le := Option.le (· ≤ ·)

@[always_inline]
instance : Functor Option where
  map := Option.map

@[always_inline]
instance : Monad Option where
  pure := Option.some
  bind := Option.bind

@[always_inline]
instance : Alternative Option where
  failure := Option.none
  orElse  := Option.orElse

def liftOption [Alternative m] : Option α → m α
  | some a => pure a
  | none   => failure

/--
Recover from failing `Option` computations with a handler function.

This function is usually accessed through the `MonadExceptOf Unit Option` instance.

Examples:
 * `Option.tryCatch none (fun () => some "handled") = some "handled"`
 * `Option.tryCatch (some "succeeded") (fun () => some "handled") = some "succeeded"`
-/
@[always_inline, inline] protected def Option.tryCatch (x : Option α) (handle : Unit → Option α) : Option α :=
  match x with
  | some _ => x
  | none => handle ()

instance : MonadExceptOf Unit Option where
  throw    := fun _ => Option.none
  tryCatch := Option.tryCatch

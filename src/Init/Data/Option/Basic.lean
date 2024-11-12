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

@[deprecated getM (since := "2024-04-17")]
-- `[Monad m]` is not needed here.
def toMonad [Monad m] [Alternative m] : Option α → m α := getM

/-- Returns `true` on `some x` and `false` on `none`. -/
@[inline] def isSome : Option α → Bool
  | some _ => true
  | none   => false

@[simp] theorem isSome_none : @isSome α none = false := rfl
@[simp] theorem isSome_some : isSome (some a) = true := rfl

@[deprecated isSome (since := "2024-04-17"), inline] def toBool : Option α → Bool := isSome

/-- Returns `true` on `none` and `false` on `some x`. -/
@[inline] def isNone : Option α → Bool
  | some _ => false
  | none   => true

@[simp] theorem isNone_none : @isNone α none = true := rfl
@[simp] theorem isNone_some : isNone (some a) = false := rfl

/--
`x?.isEqSome y` is equivalent to `x? == some y`, but avoids an allocation.
-/
@[inline] def isEqSome [BEq α] : Option α → α → Bool
  | some a, b => a == b
  | none,   _ => false

@[inline] protected def bind : Option α → (α → Option β) → Option β
  | none,   _ => none
  | some a, f => f a

/-- Runs `f` on `o`'s value, if any, and returns its result, or else returns `none`.  -/
@[inline] protected def bindM [Monad m] (f : α → m (Option β)) (o : Option α) : m (Option β) := do
  if let some a := o then
    return (← f a)
  else
    return none

/--
Runs a monadic function `f` on an optional value.
If the optional value is `none` the function is not called.
-/
@[inline] protected def mapM [Monad m] (f : α → m β) (o : Option α) : m (Option β) := do
  if let some a := o then
    return some (← f a)
  else
    return none

theorem map_id : (Option.map id : Option α → Option α) = id :=
  funext (fun o => match o with | none => rfl | some _ => rfl)

/-- Keeps an optional value only if it satisfies the predicate `p`. -/
@[always_inline, inline] protected def filter (p : α → Bool) : Option α → Option α
  | some a => if p a then some a else none
  | none   => none

/-- Checks that an optional value satisfies a predicate `p` or is `none`. -/
@[always_inline, inline] protected def all (p : α → Bool) : Option α → Bool
  | some a => p a
  | none   => true

/-- Checks that an optional value is not `none` and the value satisfies a predicate `p`. -/
@[always_inline, inline] protected def any (p : α → Bool) : Option α → Bool
  | some a => p a
  | none   => false

/--
Implementation of `OrElse`'s `<|>` syntax for `Option`. If the first argument is `some a`, returns
`some a`, otherwise evaluates and returns the second argument. See also `or` for a version that is
strict in the second argument.
-/
@[always_inline, macro_inline] protected def orElse : Option α → (Unit → Option α) → Option α
  | some a, _ => some a
  | none,   b => b ()

instance : OrElse (Option α) where
  orElse := Option.orElse

/-- If the first argument is `some a`, returns `some a`, otherwise returns the second argument.
This is similar to `<|>`/`orElse`, but it is strict in the second argument. -/
@[always_inline, macro_inline] def or : Option α → Option α → Option α
  | some a, _ => some a
  | none,   b => b

@[inline] protected def lt (r : α → α → Prop) : Option α → Option α → Prop
  | none, some _     => True
  | some x,   some y => r x y
  | _, _             => False

instance (r : α → α → Prop) [s : DecidableRel r] : DecidableRel (Option.lt r)
  | none,   some _ => isTrue  trivial
  | some x, some y => s x y
  | some _, none   => isFalse not_false
  | none,   none   => isFalse not_false

/-- Take a pair of options and if they are both `some`, apply the given fn to produce an output.
Otherwise act like `orElse`. -/
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


/-- An elimination principle for `Option`. It is a nondependent version of `Option.recOn`. -/
@[inline] protected def elim : Option α → β → (α → β) → β
  | some x, _, f => f x
  | none, y, _ => y

/-- Extracts the value `a` from an option that is known to be `some a` for some `a`. -/
@[inline] def get {α : Type u} : (o : Option α) → isSome o → α
  | some x, _ => x

@[simp] theorem some_get : ∀ {x : Option α} (h : isSome x), some (x.get h) = x
| some _, _ => rfl
@[simp] theorem get_some (x : α) (h : isSome (some x)) : (some x).get h = x := rfl

/-- `guard p a` returns `some a` if `p a` holds, otherwise `none`. -/
@[inline] def guard (p : α → Prop) [DecidablePred p] (a : α) : Option α :=
  if p a then some a else none

/--
Cast of `Option` to `List`. Returns `[a]` if the input is `some a`, and `[]` if it is `none`.
-/
@[inline] def toList : Option α → List α
  | none => .nil
  | some a => .cons a .nil

/--
Cast of `Option` to `Array`. Returns `#[a]` if the input is `some a`, and `#[]` if it is `none`.
-/
@[inline] def toArray : Option α → Array α
  | none => List.toArray .nil
  | some a => List.toArray (.cons a .nil)

/--
Two arguments failsafe function. Returns `f a b` if the inputs are `some a` and `some b`, and
"does nothing" otherwise.
-/
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

/-- Flatten an `Option` of `Option`, a specialization of `joinM`. -/
@[simp, inline] def join (x : Option (Option α)) : Option α := x.bind id

/-- Like `Option.mapM` but for applicative functors. -/
@[inline] protected def mapA [Applicative m] {α β} (f : α → m β) : Option α → m (Option β)
  | none => pure none
  | some x => some <$> f x

/--
If you maybe have a monadic computation in a `[Monad m]` which produces a term of type `α`, then
there is a naturally associated way to always perform a computation in `m` which maybe produces a
result.
-/
@[inline] def sequence [Monad m] {α : Type u} : Option (m α) → m (Option α)
  | none => pure none
  | some fn => some <$> fn

/-- A monadic analogue of `Option.elim`. -/
@[inline] def elimM [Monad m] (x : m (Option α)) (y : m β) (z : α → m β) : m β :=
  do (← x).elim y z

/-- A monadic analogue of `Option.getD`. -/
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

/-- The minimum of two optional values. -/
protected def min [Min α] : Option α → Option α → Option α
  | some x, some y => some (Min.min x y)
  | some x, none => some x
  | none, some y => some y
  | none, none => none

instance [Min α] : Min (Option α) where min := Option.min

@[simp] theorem min_some_some [Min α] {a b : α} : min (some a) (some b) = some (min a b) := rfl
@[simp] theorem min_some_none [Min α] {a : α} : min (some a) none = some a := rfl
@[simp] theorem min_none_some [Min α] {b : α} : min none (some b) = some b := rfl
@[simp] theorem min_none_none [Min α] : min (none : Option α) none = none := rfl

/-- The maximum of two optional values. -/
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

@[always_inline, inline] protected def Option.tryCatch (x : Option α) (handle : Unit → Option α) : Option α :=
  match x with
  | some _ => x
  | none => handle ()

instance : MonadExceptOf Unit Option where
  throw    := fun _ => Option.none
  tryCatch := Option.tryCatch

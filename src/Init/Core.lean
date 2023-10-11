/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura

notation, basic datatypes and type classes
-/
prelude
import Init.Prelude
import Init.SizeOf
set_option linter.missingDocs true -- keep it documented

universe u v w

/--
`inline (f x)` is an indication to the compiler to inline the definition of `f`
at the application site itself (by comparison to the `@[inline]` attribute,
which applies to all applications of the function).
-/
def inline {α : Sort u} (a : α) : α := a

/--
`flip f a b` is `f b a`. It is useful for "point-free" programming,
since it can sometimes be used to avoid introducing variables.
For example, `(·<·)` is the less-than relation,
and `flip (·<·)` is the greater-than relation.
-/
@[inline] def flip {α : Sort u} {β : Sort v} {φ : Sort w} (f : α → β → φ) : β → α → φ :=
  fun b a => f a b

@[simp] theorem Function.const_apply {y : β} {x : α} : const α y x = y := rfl

@[simp] theorem Function.comp_apply {f : β → δ} {g : α → β} {x : α} : comp f g x = f (g x) := rfl

attribute [simp] namedPattern

/--
  Thunks are "lazy" values that are evaluated when first accessed using `Thunk.get/map/bind`.
  The value is then stored and not recomputed for all further accesses. -/
-- NOTE: the runtime has special support for the `Thunk` type to implement this behavior
structure Thunk (α : Type u) : Type u where
  /-- Constructs a new thunk from a function `Unit → α`
  that will be called when the thunk is forced. -/
  mk ::
  /-- Extract the getter function out of a thunk. Use `Thunk.get` instead. -/
  private fn : Unit → α

attribute [extern "lean_mk_thunk"] Thunk.mk

/-- Store a value in a thunk. Note that the value has already been computed, so there is no laziness. -/
@[extern "lean_thunk_pure"] protected def Thunk.pure (a : α) : Thunk α :=
  ⟨fun _ => a⟩

/--
Forces a thunk to extract the value. This will cache the result,
so a second call to the same function will return the value in O(1)
instead of calling the stored getter function.
-/
-- NOTE: we use `Thunk.get` instead of `Thunk.fn` as the accessor primitive as the latter has an additional `Unit` argument
@[extern "lean_thunk_get_own"] protected def Thunk.get (x : @& Thunk α) : α :=
  x.fn ()

/-- Map a function over a thunk. -/
@[inline] protected def Thunk.map (f : α → β) (x : Thunk α) : Thunk β :=
  ⟨fun _ => f x.get⟩
/-- Constructs a thunk that applies `f` to the result of `x` when forced. -/
@[inline] protected def Thunk.bind (x : Thunk α) (f : α → Thunk β) : Thunk β :=
  ⟨fun _ => (f x.get).get⟩

@[simp] theorem Thunk.sizeOf_eq [SizeOf α] (a : Thunk α) : sizeOf a = 1 + sizeOf a.get := by
   cases a; rfl

instance thunkCoe : CoeTail α (Thunk α) where
  -- Since coercions are expanded eagerly, `a` is evaluated lazily.
  coe a := ⟨fun _ => a⟩

/-- A variation on `Eq.ndrec` with the equality argument first. -/
abbrev Eq.ndrecOn.{u1, u2} {α : Sort u2} {a : α} {motive : α → Sort u1} {b : α} (h : a = b) (m : motive a) : motive b :=
  Eq.ndrec m h

/--
If and only if, or logical bi-implication. `a ↔ b` means that `a` implies `b` and vice versa.
By `propext`, this implies that `a` and `b` are equal and hence any expression involving `a`
is equivalent to the corresponding expression with `b` instead.
-/
structure Iff (a b : Prop) : Prop where
  /-- If `a → b` and `b → a` then `a` and `b` are equivalent. -/
  intro ::
  /-- Modus ponens for if and only if. If `a ↔ b` and `a`, then `b`. -/
  mp : a → b
  /-- Modus ponens for if and only if, reversed. If `a ↔ b` and `b`, then `a`. -/
  mpr : b → a

@[inherit_doc] infix:20 " <-> " => Iff
@[inherit_doc] infix:20 " ↔ "   => Iff

/--
`Sum α β`, or `α ⊕ β`, is the disjoint union of types `α` and `β`.
An element of `α ⊕ β` is either of the form `.inl a` where `a : α`,
or `.inr b` where `b : β`.
-/
inductive Sum (α : Type u) (β : Type v) where
  /-- Left injection into the sum type `α ⊕ β`. If `a : α` then `.inl a : α ⊕ β`. -/
  | inl (val : α) : Sum α β
  /-- Right injection into the sum type `α ⊕ β`. If `b : β` then `.inr b : α ⊕ β`. -/
  | inr (val : β) : Sum α β

@[inherit_doc] infixr:30 " ⊕ " => Sum

/--
`PSum α β`, or `α ⊕' β`, is the disjoint union of types `α` and `β`.
It differs from `α ⊕ β` in that it allows `α` and `β` to have arbitrary sorts
`Sort u` and `Sort v`, instead of restricting to `Type u` and `Type v`. This means
that it can be used in situations where one side is a proposition, like `True ⊕' Nat`.

The reason this is not the default is that this type lives in the universe `Sort (max 1 u v)`,
which can cause problems for universe level unification,
because the equation `max 1 u v = ?u + 1` has no solution in level arithmetic.
`PSum` is usually only used in automation that constructs sums of arbitrary types.
-/
inductive PSum (α : Sort u) (β : Sort v) where
  /-- Left injection into the sum type `α ⊕' β`. If `a : α` then `.inl a : α ⊕' β`. -/
  | inl (val : α) : PSum α β
  /-- Right injection into the sum type `α ⊕' β`. If `b : β` then `.inr b : α ⊕' β`. -/
  | inr (val : β) : PSum α β

@[inherit_doc] infixr:30 " ⊕' " => PSum

/--
`Sigma β`, also denoted `Σ a : α, β a` or `(a : α) × β a`, is the type of dependent pairs
whose first component is `a : α` and whose second component is `b : β a`
(so the type of the second component can depend on the value of the first component).
It is sometimes known as the dependent sum type, since it is the type level version
of an indexed summation.
-/
structure Sigma {α : Type u} (β : α → Type v) where
  /-- Constructor for a dependent pair. If `a : α` and `b : β a` then `⟨a, b⟩ : Sigma β`.
  (This will usually require a type ascription to determine `β`
  since it is not determined from `a` and `b` alone.) -/
  mk ::
  /-- The first component of a dependent pair. If `p : @Sigma α β` then `p.1 : α`. -/
  fst : α
  /-- The second component of a dependent pair. If `p : Sigma β` then `p.2 : β p.1`. -/
  snd : β fst

attribute [unbox] Sigma

/--
`PSigma β`, also denoted `Σ' a : α, β a` or `(a : α) ×' β a`, is the type of dependent pairs
whose first component is `a : α` and whose second component is `b : β a`
(so the type of the second component can depend on the value of the first component).
It differs from `Σ a : α, β a` in that it allows `α` and `β` to have arbitrary sorts
`Sort u` and `Sort v`, instead of restricting to `Type u` and `Type v`. This means
that it can be used in situations where one side is a proposition, like `(p : Nat) ×' p = p`.

The reason this is not the default is that this type lives in the universe `Sort (max 1 u v)`,
which can cause problems for universe level unification,
because the equation `max 1 u v = ?u + 1` has no solution in level arithmetic.
`PSigma` is usually only used in automation that constructs pairs of arbitrary types.
-/
structure PSigma {α : Sort u} (β : α → Sort v) where
  /-- Constructor for a dependent pair. If `a : α` and `b : β a` then `⟨a, b⟩ : PSigma β`.
  (This will usually require a type ascription to determine `β`
  since it is not determined from `a` and `b` alone.) -/
  mk ::
  /-- The first component of a dependent pair. If `p : @Sigma α β` then `p.1 : α`. -/
  fst : α
  /-- The second component of a dependent pair. If `p : Sigma β` then `p.2 : β p.1`. -/
  snd : β fst

/--
Existential quantification. If `p : α → Prop` is a predicate, then `∃ x : α, p x`
asserts that there is some `x` of type `α` such that `p x` holds.
To create an existential proof, use the `exists` tactic,
or the anonymous constructor notation `⟨x, h⟩`.
To unpack an existential, use `cases h` where `h` is a proof of `∃ x : α, p x`,
or `let ⟨x, hx⟩ := h` where `.

Because Lean has proof irrelevance, any two proofs of an existential are
definitionally equal. One consequence of this is that it is impossible to recover the
witness of an existential from the mere fact of its existence.
For example, the following does not compile:
```
example (h : ∃ x : Nat, x = x) : Nat :=
  let ⟨x, _⟩ := h  -- fail, because the goal is `Nat : Type`
  x
```
The error message `recursor 'Exists.casesOn' can only eliminate into Prop` means
that this only works when the current goal is another proposition:
```
example (h : ∃ x : Nat, x = x) : True :=
  let ⟨x, _⟩ := h  -- ok, because the goal is `True : Prop`
  trivial
```
-/
inductive Exists {α : Sort u} (p : α → Prop) : Prop where
  /-- Existential introduction. If `a : α` and `h : p a`,
  then `⟨a, h⟩` is a proof that `∃ x : α, p x`. -/
  | intro (w : α) (h : p w) : Exists p

/--
Auxiliary type used to compile `for x in xs` notation.

This is the return value of the body of a `ForIn` call,
representing the body of a for loop. It can be:

* `.yield (a : α)`, meaning that we should continue the loop and `a` is the new state.
  `.yield` is produced by `continue` and reaching the bottom of the loop body.
* `.done (a : α)`, meaning that we should early-exit the loop with state `a`.
  `.done` is produced by calls to `break` or `return` in the loop,
-/
inductive ForInStep (α : Type u) where
  /-- `.done a` means that we should early-exit the loop.
  `.done` is produced by calls to `break` or `return` in the loop. -/
  | done  : α → ForInStep α
  /-- `.yield a` means that we should continue the loop.
  `.yield` is produced by `continue` and reaching the bottom of the loop body. -/
  | yield : α → ForInStep α
  deriving Inhabited

/--
`ForIn m ρ α` is the typeclass which supports `for x in xs` notation.
Here `xs : ρ` is the type of the collection to iterate over, `x : α`
is the element type which is made available inside the loop, and `m` is the monad
for the encompassing `do` block.
-/
class ForIn (m : Type u₁ → Type u₂) (ρ : Type u) (α : outParam (Type v)) where
  /-- `forIn x b f : m β` runs a for-loop in the monad `m` with additional state `β`.
  This traverses over the "contents" of `x`, and passes the elements `a : α` to
  `f : α → β → m (ForInStep β)`. `b : β` is the initial state, and the return value
  of `f` is the new state as well as a directive `.done` or `.yield`
  which indicates whether to abort early or continue iteration.

  The expression
  ```
  let mut b := ...
  for x in xs do
    b ← foo x b
  ```
  in a `do` block is syntactic sugar for:
  ```
  let b := ...
  let b ← forIn xs b (fun x b => do
    let b ← foo x b
    return .yield b)
  ```
  (Here `b` corresponds to the variables mutated in the loop.) -/
  forIn {β} [Monad m] (x : ρ) (b : β) (f : α → β → m (ForInStep β)) : m β

export ForIn (forIn)

/--
`ForIn' m ρ α d` is a variation on the `ForIn m ρ α` typeclass which supports the
`for h : x in xs` notation. It is the same as `for x in xs` except that `h : x ∈ xs`
is provided as an additional argument to the body of the for-loop.
-/
class ForIn' (m : Type u₁ → Type u₂) (ρ : Type u) (α : outParam (Type v)) (d : outParam $ Membership α ρ) where
  /-- `forIn' x b f : m β` runs a for-loop in the monad `m` with additional state `β`.
  This traverses over the "contents" of `x`, and passes the elements `a : α` along
  with a proof that `a ∈ x` to `f : (a : α) → a ∈ x → β → m (ForInStep β)`.
  `b : β` is the initial state, and the return value
  of `f` is the new state as well as a directive `.done` or `.yield`
  which indicates whether to abort early or continue iteration. -/
  forIn' {β} [Monad m] (x : ρ) (b : β) (f : (a : α) → a ∈ x → β → m (ForInStep β)) : m β

export ForIn' (forIn')


/--
Auxiliary type used to compile `do` notation. It is used when compiling a do block
nested inside a combinator like `tryCatch`. It encodes the possible ways the
block can exit:
* `pure (a : α) s` means that the block exited normally with return value `a`.
* `return (b : β) s` means that the block exited via a `return b` early-exit command.
* `break s` means that `break` was called, meaning that we should exit
  from the containing loop.
* `continue s` means that `continue` was called, meaning that we should continue
  to the next iteration of the containing loop.

All cases return a value `s : σ` which bundles all the mutable variables of the do-block.
-/
inductive DoResultPRBC (α β σ : Type u) where
  /-- `pure (a : α) s` means that the block exited normally with return value `a` -/
  | pure : α → σ → DoResultPRBC α β σ
  /-- `return (b : β) s` means that the block exited via a `return b` early-exit command -/
  | return : β → σ → DoResultPRBC α β σ
  /-- `break s` means that `break` was called, meaning that we should exit
  from the containing loop -/
  | break : σ → DoResultPRBC α β σ
  /-- `continue s` means that `continue` was called, meaning that we should continue
  to the next iteration of the containing loop -/
  | continue : σ → DoResultPRBC α β σ

/--
Auxiliary type used to compile `do` notation. It is the same as
`DoResultPRBC α β σ` except that `break` and `continue` are not available
because we are not in a loop context.
-/
inductive DoResultPR (α β σ : Type u) where
  /-- `pure (a : α) s` means that the block exited normally with return value `a` -/
  | pure   : α → σ → DoResultPR α β σ
  /-- `return (b : β) s` means that the block exited via a `return b` early-exit command -/
  | return : β → σ → DoResultPR α β σ

/--
Auxiliary type used to compile `do` notation. It is an optimization of
`DoResultPRBC PEmpty PEmpty σ` to remove the impossible cases,
used when neither `pure` nor `return` are possible exit paths.
-/
inductive DoResultBC (σ : Type u) where
  /-- `break s` means that `break` was called, meaning that we should exit
  from the containing loop -/
  | break    : σ → DoResultBC σ
  /-- `continue s` means that `continue` was called, meaning that we should continue
  to the next iteration of the containing loop -/
  | continue : σ → DoResultBC σ

/--
Auxiliary type used to compile `do` notation. It is an optimization of
either `DoResultPRBC α PEmpty σ` or `DoResultPRBC PEmpty α σ` to remove the
impossible case, used when either `pure` or `return` is never used.
-/
inductive DoResultSBC (α σ : Type u) where
  /-- This encodes either `pure (a : α)` or `return (a : α)`:
  * `pure (a : α) s` means that the block exited normally with return value `a`
  * `return (b : β) s` means that the block exited via a `return b` early-exit command

  The one that is actually encoded depends on the context of use. -/
  | pureReturn : α → σ → DoResultSBC α σ
  /-- `break s` means that `break` was called, meaning that we should exit
  from the containing loop -/
  | break    : σ → DoResultSBC α σ
  /-- `continue s` means that `continue` was called, meaning that we should continue
  to the next iteration of the containing loop -/
  | continue   : σ → DoResultSBC α σ

/-- `HasEquiv α` is the typeclass which supports the notation `x ≈ y` where `x y : α`.-/
class HasEquiv (α : Sort u) where
  /-- `x ≈ y` says that `x` and `y` are equivalent. Because this is a typeclass,
  the notion of equivalence is type-dependent. -/
  Equiv : α → α → Sort v

@[inherit_doc] infix:50 " ≈ "  => HasEquiv.Equiv

/-- `EmptyCollection α` is the typeclass which supports the notation `∅`, also written as `{}`. -/
class EmptyCollection (α : Type u) where
  /-- `∅` or `{}` is the empty set or empty collection.
  It is supported by the `EmptyCollection` typeclass. -/
  emptyCollection : α

@[inherit_doc] notation "{" "}" => EmptyCollection.emptyCollection
@[inherit_doc] notation "∅"     => EmptyCollection.emptyCollection

/--
`Task α` is a primitive for asynchronous computation.
It represents a computation that will resolve to a value of type `α`,
possibly being computed on another thread. This is similar to `Future` in Scala,
`Promise` in Javascript, and `JoinHandle` in Rust.

The tasks have an overridden representation in the runtime.
-/
structure Task (α : Type u) : Type u where
  /-- `Task.pure (a : α)` constructs a task that is already resolved with value `a`. -/
  pure ::
  /-- If `task : Task α` then `task.get : α` blocks the current thread until the
  value is available, and then returns the result of the task. -/
  get : α
  deriving Inhabited, Nonempty

attribute [extern "lean_task_pure"] Task.pure
attribute [extern "lean_task_get_own"] Task.get

namespace Task
/-- Task priority. Tasks with higher priority will always be scheduled before ones with lower priority. -/
abbrev Priority := Nat

/-- The default priority for spawned tasks, also the lowest priority: `0`. -/
def Priority.default : Priority := 0
/--
The highest regular priority for spawned tasks: `8`.

Spawning a task with a priority higher than `Task.Priority.max` is not an error but
will spawn a dedicated worker for the task, see `Task.Priority.dedicated`.
Regular priority tasks are placed in a thread pool and worked on according to the priority order.
-/
-- see `LEAN_MAX_PRIO`
def Priority.max : Priority := 8
/--
Any priority higher than `Task.Priority.max` will result in the task being scheduled
immediately on a dedicated thread. This is particularly useful for long-running and/or
I/O-bound tasks since Lean will by default allocate no more non-dedicated workers
than the number of cores to reduce context switches.
-/
def Priority.dedicated : Priority := 9

set_option linter.unusedVariables.funArgs false in
/--
`spawn fn : Task α` constructs and immediately launches a new task for
evaluating the function `fn () : α` asynchronously.

`prio`, if provided, is the priority of the task.
-/
@[noinline, extern "lean_task_spawn"]
protected def spawn {α : Type u} (fn : Unit → α) (prio := Priority.default) : Task α :=
  ⟨fn ()⟩

set_option linter.unusedVariables.funArgs false in
/--
`map f x` maps function `f` over the task `x`: that is, it constructs
(and immediately launches) a new task which will wait for the value of `x` to
be available and then calls `f` on the result.

`prio`, if provided, is the priority of the task.
-/
@[noinline, extern "lean_task_map"]
protected def map {α : Type u} {β : Type v} (f : α → β) (x : Task α) (prio := Priority.default) : Task β :=
  ⟨f x.get⟩

set_option linter.unusedVariables.funArgs false in
/--
`bind x f` does a monad "bind" operation on the task `x` with function `f`:
that is, it constructs (and immediately launches) a new task which will wait
for the value of `x` to be available and then calls `f` on the result,
resulting in a new task which is then run for a result.

`prio`, if provided, is the priority of the task.
-/
@[noinline, extern "lean_task_bind"]
protected def bind {α : Type u} {β : Type v} (x : Task α) (f : α → Task β) (prio := Priority.default) : Task β :=
  ⟨(f x.get).get⟩

end Task

/--
`NonScalar` is a type that is not a scalar value in our runtime.
It is used as a stand-in for an arbitrary boxed value to avoid excessive
monomorphization, and it is only created using `unsafeCast`. It is somewhat
analogous to C `void*` in usage, but the type itself is not special.
-/
structure NonScalar where
  /-- You should not use this function -/ mk ::
  /-- You should not use this function -/ val : Nat

/--
`PNonScalar` is a type that is not a scalar value in our runtime.
It is used as a stand-in for an arbitrary boxed value to avoid excessive
monomorphization, and it is only created using `unsafeCast`. It is somewhat
analogous to C `void*` in usage, but the type itself is not special.

This is the universe-polymorphic version of `PNonScalar`; it is preferred to use
`NonScalar` instead where applicable.
-/
inductive PNonScalar : Type u where
  /-- You should not use this function -/
  | mk (v : Nat) : PNonScalar

@[simp] protected theorem Nat.add_zero (n : Nat) : n + 0 = n := rfl

theorem optParam_eq (α : Sort u) (default : α) : optParam α default = α := rfl

/-! # Boolean operators -/

/--
`strictOr` is the same as `or`, but it does not use short-circuit evaluation semantics:
both sides are evaluated, even if the first value is `true`.
-/
@[extern "lean_strict_or"] def strictOr  (b₁ b₂ : Bool) := b₁ || b₂

/--
`strictAnd` is the same as `and`, but it does not use short-circuit evaluation semantics:
both sides are evaluated, even if the first value is `false`.
-/
@[extern "lean_strict_and"] def strictAnd (b₁ b₂ : Bool) := b₁ && b₂

/--
`x != y` is boolean not-equal. It is the negation of `x == y` which is supplied by
the `BEq` typeclass.

Unlike `x ≠ y` (which is notation for `Ne x y`), this is `Bool` valued instead of
`Prop` valued. It is mainly intended for programming applications.
-/
@[inline] def bne {α : Type u} [BEq α] (a b : α) : Bool :=
  !(a == b)

@[inherit_doc] infix:50 " != " => bne

/--
`LawfulBEq α` is a typeclass which asserts that the `BEq α` implementation
(which supplies the `a == b` notation) coincides with logical equality `a = b`.
In other words, `a == b` implies `a = b`, and `a == a` is true.
-/
class LawfulBEq (α : Type u) [BEq α] : Prop where
  /-- If `a == b` evaluates to `true`, then `a` and `b` are equal in the logic. -/
  eq_of_beq : {a b : α} → a == b → a = b
  /-- `==` is reflexive, that is, `(a == a) = true`. -/
  protected rfl : {a : α} → a == a

export LawfulBEq (eq_of_beq)

instance : LawfulBEq Bool where
  eq_of_beq {a b} h := by cases a <;> cases b <;> first | rfl | contradiction
  rfl {a} := by cases a <;> decide

instance [DecidableEq α] : LawfulBEq α where
  eq_of_beq := of_decide_eq_true
  rfl := of_decide_eq_self_eq_true _

instance : LawfulBEq Char := inferInstance

instance : LawfulBEq String := inferInstance

/-! # Logical connectives and equality -/

@[inherit_doc True.intro] def trivial : True := ⟨⟩

theorem mt {a b : Prop} (h₁ : a → b) (h₂ : ¬b) : ¬a :=
  fun ha => h₂ (h₁ ha)

theorem not_false : ¬False := id

theorem not_not_intro {p : Prop} (h : p) : ¬ ¬ p :=
  fun hn : ¬ p => hn h

-- proof irrelevance is built in
theorem proofIrrel {a : Prop} (h₁ h₂ : a) : h₁ = h₂ := rfl

theorem id.def {α : Sort u} (a : α) : id a = a := rfl

/--
If `h : α = β` is a proof of type equality, then `h.mp : α → β` is the induced
"cast" operation, mapping elements of `α` to elements of `β`.

You can prove theorems about the resulting element by induction on `h`, since
`rfl.mp` is definitionally the identity function.
-/
@[macro_inline] def Eq.mp {α β : Sort u} (h : α = β) (a : α) : β :=
  h ▸ a

/--
If `h : α = β` is a proof of type equality, then `h.mpr : β → α` is the induced
"cast" operation in the reverse direction, mapping elements of `β` to elements of `α`.

You can prove theorems about the resulting element by induction on `h`, since
`rfl.mpr` is definitionally the identity function.
-/
@[macro_inline] def Eq.mpr {α β : Sort u} (h : α = β) (b : β) : α :=
  h ▸ b

@[elab_as_elim]
theorem Eq.substr {α : Sort u} {p : α → Prop} {a b : α} (h₁ : b = a) (h₂ : p a) : p b :=
  h₁ ▸ h₂

theorem cast_eq {α : Sort u} (h : α = α) (a : α) : cast h a = a :=
  rfl

/--
`a ≠ b`, or `Ne a b` is defined as `¬ (a = b)` or `a = b → False`,
and asserts that `a` and `b` are not equal.
-/
@[reducible] def Ne {α : Sort u} (a b : α) :=
  ¬(a = b)

@[inherit_doc] infix:50 " ≠ "  => Ne

section Ne
variable {α : Sort u}
variable {a b : α} {p : Prop}

theorem Ne.intro (h : a = b → False) : a ≠ b := h

theorem Ne.elim (h : a ≠ b) : a = b → False := h

theorem Ne.irrefl (h : a ≠ a) : False := h rfl

theorem Ne.symm (h : a ≠ b) : b ≠ a :=
  fun h₁ => h (h₁.symm)

theorem false_of_ne : a ≠ a → False := Ne.irrefl

theorem ne_false_of_self : p → p ≠ False :=
  fun (hp : p) (h : p = False) => h ▸ hp

theorem ne_true_of_not : ¬p → p ≠ True :=
  fun (hnp : ¬p) (h : p = True) =>
    have : ¬True := h ▸ hnp
    this trivial

theorem true_ne_false : ¬True = False :=
  ne_false_of_self trivial

end Ne

theorem Bool.of_not_eq_true : {b : Bool} → ¬ (b = true) → b = false
  | true,  h => absurd rfl h
  | false, _ => rfl

theorem Bool.of_not_eq_false : {b : Bool} → ¬ (b = false) → b = true
  | true,  _ => rfl
  | false, h => absurd rfl h

theorem ne_of_beq_false [BEq α] [LawfulBEq α] {a b : α} (h : (a == b) = false) : a ≠ b := by
  intro h'; subst h'; have : true = false := Eq.trans LawfulBEq.rfl.symm h; contradiction

theorem beq_false_of_ne [BEq α] [LawfulBEq α] {a b : α} (h : a ≠ b) : (a == b) = false :=
  have : ¬ (a == b) = true := by
    intro h'; rw [eq_of_beq h'] at h; contradiction
  Bool.of_not_eq_true this

section
variable {α β φ : Sort u} {a a' : α} {b b' : β} {c : φ}

theorem HEq.ndrec.{u1, u2} {α : Sort u2} {a : α} {motive : {β : Sort u2} → β → Sort u1} (m : motive a) {β : Sort u2} {b : β} (h : HEq a b) : motive b :=
  h.rec m

theorem HEq.ndrecOn.{u1, u2} {α : Sort u2} {a : α} {motive : {β : Sort u2} → β → Sort u1} {β : Sort u2} {b : β} (h : HEq a b) (m : motive a) : motive b :=
  h.rec m

theorem HEq.elim {α : Sort u} {a : α} {p : α → Sort v} {b : α} (h₁ : HEq a b) (h₂ : p a) : p b :=
  eq_of_heq h₁ ▸ h₂

theorem HEq.subst {p : (T : Sort u) → T → Prop} (h₁ : HEq a b) (h₂ : p α a) : p β b :=
  HEq.ndrecOn h₁ h₂

theorem HEq.symm (h : HEq a b) : HEq b a :=
  h.rec (HEq.refl a)

theorem heq_of_eq (h : a = a') : HEq a a' :=
  Eq.subst h (HEq.refl a)

theorem HEq.trans (h₁ : HEq a b) (h₂ : HEq b c) : HEq a c :=
  HEq.subst h₂ h₁

theorem heq_of_heq_of_eq (h₁ : HEq a b) (h₂ : b = b') : HEq a b' :=
  HEq.trans h₁ (heq_of_eq h₂)

theorem heq_of_eq_of_heq (h₁ : a = a') (h₂ : HEq a' b) : HEq a b :=
  HEq.trans (heq_of_eq h₁) h₂

theorem type_eq_of_heq (h : HEq a b) : α = β :=
  h.rec (Eq.refl α)

end

theorem eqRec_heq {α : Sort u} {φ : α → Sort v} {a a' : α} : (h : a = a') → (p : φ a) → HEq (Eq.recOn (motive := fun x _ => φ x) h p) p
  | rfl, p => HEq.refl p

theorem heq_of_eqRec_eq {α β : Sort u} {a : α} {b : β} (h₁ : α = β) (h₂ : Eq.rec (motive := fun α _ => α) a h₁ = b) : HEq a b := by
  subst h₁
  apply heq_of_eq
  exact h₂

theorem cast_heq {α β : Sort u} : (h : α = β) → (a : α) → HEq (cast h a) a
  | rfl, a => HEq.refl a

variable {a b c d : Prop}

theorem iff_iff_implies_and_implies (a b : Prop) : (a ↔ b) ↔ (a → b) ∧ (b → a) :=
  Iff.intro (fun h => And.intro h.mp h.mpr) (fun h => Iff.intro h.left h.right)

theorem Iff.refl (a : Prop) : a ↔ a :=
  Iff.intro (fun h => h) (fun h => h)

protected theorem Iff.rfl {a : Prop} : a ↔ a :=
  Iff.refl a

theorem Iff.trans (h₁ : a ↔ b) (h₂ : b ↔ c) : a ↔ c :=
  Iff.intro
    (fun ha => Iff.mp h₂ (Iff.mp h₁ ha))
    (fun hc => Iff.mpr h₁ (Iff.mpr h₂ hc))

theorem Iff.symm (h : a ↔ b) : b ↔ a :=
  Iff.intro (Iff.mpr h) (Iff.mp h)

theorem Iff.comm : (a ↔ b) ↔ (b ↔ a) :=
  Iff.intro Iff.symm Iff.symm

theorem Iff.of_eq (h : a = b) : a ↔ b :=
  h ▸ Iff.refl _

theorem And.comm : a ∧ b ↔ b ∧ a := by
  constructor <;> intro ⟨h₁, h₂⟩ <;> exact ⟨h₂, h₁⟩

/-! # Exists -/

theorem Exists.elim {α : Sort u} {p : α → Prop} {b : Prop}
   (h₁ : Exists (fun x => p x)) (h₂ : ∀ (a : α), p a → b) : b :=
  match h₁ with
  | intro a h => h₂ a h

/-! # Decidable -/

theorem decide_true_eq_true (h : Decidable True) : @decide True h = true :=
  match h with
  | isTrue _  => rfl
  | isFalse h => False.elim <| h ⟨⟩

theorem decide_false_eq_false (h : Decidable False) : @decide False h = false :=
  match h with
  | isFalse _ => rfl
  | isTrue h  => False.elim h

/-- Similar to `decide`, but uses an explicit instance -/
@[inline] def toBoolUsing {p : Prop} (d : Decidable p) : Bool :=
  decide (h := d)

theorem toBoolUsing_eq_true {p : Prop} (d : Decidable p) (h : p) : toBoolUsing d = true :=
  decide_eq_true (inst := d) h

theorem ofBoolUsing_eq_true {p : Prop} {d : Decidable p} (h : toBoolUsing d = true) : p :=
  of_decide_eq_true (inst := d) h

theorem ofBoolUsing_eq_false {p : Prop} {d : Decidable p} (h : toBoolUsing d = false) : ¬ p :=
  of_decide_eq_false (inst := d) h

instance : Decidable True :=
  isTrue trivial

instance : Decidable False :=
  isFalse not_false

namespace Decidable
variable {p q : Prop}

/--
Synonym for `dite` (dependent if-then-else). We can construct an element `q`
(of any sort, not just a proposition) by cases on whether `p` is true or false,
provided `p` is decidable.
-/
@[macro_inline] def byCases {q : Sort u} [dec : Decidable p] (h1 : p → q) (h2 : ¬p → q) : q :=
  match dec with
  | isTrue h  => h1 h
  | isFalse h => h2 h

theorem em (p : Prop) [Decidable p] : p ∨ ¬p :=
  byCases Or.inl Or.inr

set_option linter.unusedVariables.funArgs false in
theorem byContradiction [dec : Decidable p] (h : ¬p → False) : p :=
  byCases id (fun np => False.elim (h np))

theorem of_not_not [Decidable p] : ¬ ¬ p → p :=
  fun hnn => byContradiction (fun hn => absurd hn hnn)

theorem not_and_iff_or_not (p q : Prop) [d₁ : Decidable p] [d₂ : Decidable q] : ¬ (p ∧ q) ↔ ¬ p ∨ ¬ q :=
  Iff.intro
    (fun h => match d₁, d₂ with
      | isTrue h₁,  isTrue h₂   => absurd (And.intro h₁ h₂) h
      | _,           isFalse h₂ => Or.inr h₂
      | isFalse h₁, _           => Or.inl h₁)
    (fun (h) ⟨hp, hq⟩ => match h with
      | Or.inl h => h hp
      | Or.inr h => h hq)

end Decidable

section
variable {p q : Prop}
/-- Transfer a decidability proof across an equivalence of propositions. -/
@[inline] def decidable_of_decidable_of_iff [Decidable p] (h : p ↔ q) : Decidable q :=
  if hp : p then
    isTrue (Iff.mp h hp)
  else
    isFalse fun hq => absurd (Iff.mpr h hq) hp

/-- Transfer a decidability proof across an equality of propositions. -/
@[inline] def decidable_of_decidable_of_eq [Decidable p] (h : p = q) : Decidable q :=
  decidable_of_decidable_of_iff (p := p) (h ▸ Iff.rfl)
end

@[macro_inline] instance {p q} [Decidable p] [Decidable q] : Decidable (p → q) :=
  if hp : p then
    if hq : q then isTrue (fun _ => hq)
    else isFalse (fun h => absurd (h hp) hq)
  else isTrue (fun h => absurd h hp)

instance {p q} [Decidable p] [Decidable q] : Decidable (p ↔ q) :=
  if hp : p then
    if hq : q then
      isTrue ⟨fun _ => hq, fun _ => hp⟩
    else
      isFalse fun h => hq (h.1 hp)
  else
    if hq : q then
      isFalse fun h => hp (h.2 hq)
    else
      isTrue ⟨fun h => absurd h hp, fun h => absurd h hq⟩

/-! # if-then-else expression theorems -/

theorem if_pos {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t :=
  match h with
  | isTrue  _   => rfl
  | isFalse hnc => absurd hc hnc

theorem if_neg {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e :=
  match h with
  | isTrue hc   => absurd hc hnc
  | isFalse _   => rfl

/-- Split an if-then-else into cases. The `split` tactic is generally easier to use than this theorem. -/
def iteInduction {c} [inst : Decidable c] {motive : α → Sort _} {t e : α}
    (hpos : c → motive t) (hneg : ¬c → motive e) : motive (ite c t e) :=
  match inst with
  | isTrue h => hpos h
  | isFalse h => hneg h

theorem dif_pos {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α} {e : ¬ c → α} : (dite c t e) = t hc :=
  match h with
  | isTrue  _   => rfl
  | isFalse hnc => absurd hc hnc

theorem dif_neg {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c → α} {e : ¬ c → α} : (dite c t e) = e hnc :=
  match h with
  | isTrue hc   => absurd hc hnc
  | isFalse _   => rfl

-- Remark: dite and ite are "defally equal" when we ignore the proofs.
theorem dif_eq_if (c : Prop) {h : Decidable c} {α : Sort u} (t : α) (e : α) : dite c (fun _ => t) (fun _ => e) = ite c t e :=
  match h with
  | isTrue _    => rfl
  | isFalse _   => rfl

instance {c t e : Prop} [dC : Decidable c] [dT : Decidable t] [dE : Decidable e] : Decidable (if c then t else e)  :=
  match dC with
  | isTrue _   => dT
  | isFalse _  => dE

instance {c : Prop} {t : c → Prop} {e : ¬c → Prop} [dC : Decidable c] [dT : ∀ h, Decidable (t h)] [dE : ∀ h, Decidable (e h)] : Decidable (if h : c then t h else e h)  :=
  match dC with
  | isTrue hc  => dT hc
  | isFalse hc => dE hc

/-- Auxiliary definition for generating compact `noConfusion` for enumeration types -/
abbrev noConfusionTypeEnum {α : Sort u} {β : Sort v} [inst : DecidableEq β] (f : α → β) (P : Sort w) (x y : α) : Sort w :=
  (inst (f x) (f y)).casesOn
    (fun _ => P)
    (fun _ => P → P)

/-- Auxiliary definition for generating compact `noConfusion` for enumeration types -/
abbrev noConfusionEnum {α : Sort u} {β : Sort v} [inst : DecidableEq β] (f : α → β) {P : Sort w} {x y : α} (h : x = y) : noConfusionTypeEnum f P x y :=
  Decidable.casesOn
    (motive := fun (inst : Decidable (f x = f y)) => Decidable.casesOn (motive := fun _ => Sort w) inst (fun _ => P) (fun _ => P → P))
    (inst (f x) (f y))
    (fun h' => False.elim (h' (congrArg f h)))
    (fun _ => fun x => x)

/-! # Inhabited -/

instance : Inhabited Prop where
  default := True

deriving instance Inhabited for NonScalar, PNonScalar, True, ForInStep

theorem nonempty_of_exists {α : Sort u} {p : α → Prop} : Exists (fun x => p x) → Nonempty α
  | ⟨w, _⟩ => ⟨w⟩

/-! # Subsingleton -/

/--
A "subsingleton" is a type with at most one element.
In other words, it is either empty, or has a unique element.
All propositions are subsingletons because of proof irrelevance, but some other types
are subsingletons as well and they inherit many of the same properties as propositions.
`Subsingleton α` is a typeclass, so it is usually used as an implicit argument and
inferred by typeclass inference.
-/
class Subsingleton (α : Sort u) : Prop where
  /-- Construct a proof that `α` is a subsingleton by showing that any two elements are equal. -/
  intro ::
  /-- Any two elements of a subsingleton are equal. -/
  allEq : (a b : α) → a = b

protected theorem Subsingleton.elim {α : Sort u} [h : Subsingleton α] : (a b : α) → a = b :=
  h.allEq

protected theorem Subsingleton.helim {α β : Sort u} [h₁ : Subsingleton α] (h₂ : α = β) (a : α) (b : β) : HEq a b := by
  subst h₂
  apply heq_of_eq
  apply Subsingleton.elim

instance (p : Prop) : Subsingleton p :=
  ⟨fun a b => proofIrrel a b⟩

instance (p : Prop) : Subsingleton (Decidable p) :=
  Subsingleton.intro fun
    | isTrue t₁ => fun
      | isTrue _   => rfl
      | isFalse f₂ => absurd t₁ f₂
    | isFalse f₁ => fun
      | isTrue t₂  => absurd t₂ f₁
      | isFalse _  => rfl

theorem recSubsingleton
     {p : Prop} [h : Decidable p]
     {h₁ : p → Sort u}
     {h₂ : ¬p → Sort u}
     [h₃ : ∀ (h : p), Subsingleton (h₁ h)]
     [h₄ : ∀ (h : ¬p), Subsingleton (h₂ h)]
     : Subsingleton (h.casesOn h₂ h₁) :=
  match h with
  | isTrue h  => h₃ h
  | isFalse h => h₄ h

/--
An equivalence relation `~ : α → α → Prop` is a relation that is:

* reflexive: `x ~ x`
* symmetric: `x ~ y` implies `y ~ x`
* transitive: `x ~ y` and `y ~ z` implies `x ~ z`

Equality is an equivalence relation, and equivalence relations share many of
the properties of equality. In particular, `Quot α r` is most well behaved
when `r` is an equivalence relation, and in this case we use `Quotient` instead.
-/
structure Equivalence {α : Sort u} (r : α → α → Prop) : Prop where
  /-- An equivalence relation is reflexive: `x ~ x` -/
  refl  : ∀ x, r x x
  /-- An equivalence relation is symmetric: `x ~ y` implies `y ~ x` -/
  symm  : ∀ {x y}, r x y → r y x
  /-- An equivalence relation is transitive: `x ~ y` and `y ~ z` implies `x ~ z` -/
  trans : ∀ {x y z}, r x y → r y z → r x z

/-- The empty relation is the relation on `α` which is always `False`. -/
def emptyRelation {α : Sort u} (_ _ : α) : Prop :=
  False

/--
`Subrelation q r` means that `q ⊆ r` or `∀ x y, q x y → r x y`.
It is the analogue of the subset relation on relations.
-/
def Subrelation {α : Sort u} (q r : α → α → Prop) :=
  ∀ {x y}, q x y → r x y

/--
The inverse image of `r : β → β → Prop` by a function `α → β` is the relation
`s : α → α → Prop` defined by `s a b = r (f a) (f b)`.
-/
def InvImage {α : Sort u} {β : Sort v} (r : β → β → Prop) (f : α → β) : α → α → Prop :=
  fun a₁ a₂ => r (f a₁) (f a₂)

/--
The transitive closure `r⁺` of a relation `r` is the smallest relation which is
transitive and contains `r`. `r⁺ a z` if and only if there exists a sequence
`a r b r ... r z` of length at least 1 connecting `a` to `z`.
-/
inductive TC {α : Sort u} (r : α → α → Prop) : α → α → Prop where
  /-- If `r a b` then `r⁺ a b`. This is the base case of the transitive closure. -/
  | base  : ∀ a b, r a b → TC r a b
  /-- The transitive closure is transitive. -/
  | trans : ∀ a b c, TC r a b → TC r b c → TC r a c

/-! # Subtype -/

namespace Subtype
theorem existsOfSubtype {α : Type u} {p : α → Prop} : { x // p x } → Exists (fun x => p x)
  | ⟨a, h⟩ => ⟨a, h⟩

variable {α : Type u} {p : α → Prop}

protected theorem eq : ∀ {a1 a2 : {x // p x}}, val a1 = val a2 → a1 = a2
  | ⟨_, _⟩, ⟨_, _⟩, rfl => rfl

theorem eta (a : {x // p x}) (h : p (val a)) : mk (val a) h = a := by
  cases a
  exact rfl

instance {α : Type u} {p : α → Prop} {a : α} (h : p a) : Inhabited {x // p x} where
  default := ⟨a, h⟩

instance {α : Type u} {p : α → Prop} [DecidableEq α] : DecidableEq {x : α // p x} :=
  fun ⟨a, h₁⟩ ⟨b, h₂⟩ =>
    if h : a = b then isTrue (by subst h; exact rfl)
    else isFalse (fun h' => Subtype.noConfusion h' (fun h' => absurd h' h))

end Subtype

/-! # Sum -/

section
variable {α : Type u} {β : Type v}

instance Sum.inhabitedLeft [Inhabited α] : Inhabited (Sum α β) where
  default := Sum.inl default

instance Sum.inhabitedRight [Inhabited β] : Inhabited (Sum α β) where
  default := Sum.inr default

instance {α : Type u} {β : Type v} [DecidableEq α] [DecidableEq β] : DecidableEq (Sum α β) := fun a b =>
  match a, b with
  | Sum.inl a, Sum.inl b =>
    if h : a = b then isTrue (h ▸ rfl)
    else isFalse fun h' => Sum.noConfusion h' fun h' => absurd h' h
  | Sum.inr a, Sum.inr b =>
    if h : a = b then isTrue (h ▸ rfl)
    else isFalse fun h' => Sum.noConfusion h' fun h' => absurd h' h
  | Sum.inr _, Sum.inl _ => isFalse fun h => Sum.noConfusion h
  | Sum.inl _, Sum.inr _ => isFalse fun h => Sum.noConfusion h

end

/-! # Product -/

instance [Inhabited α] [Inhabited β] : Inhabited (α × β) where
  default := (default, default)

instance [Inhabited α] [Inhabited β] : Inhabited (MProd α β) where
  default := ⟨default, default⟩

instance [Inhabited α] [Inhabited β] : Inhabited (PProd α β) where
  default := ⟨default, default⟩

instance [DecidableEq α] [DecidableEq β] : DecidableEq (α × β) :=
  fun (a, b) (a', b') =>
    match decEq a a' with
    | isTrue e₁ =>
      match decEq b b' with
      | isTrue e₂  => isTrue (e₁ ▸ e₂ ▸ rfl)
      | isFalse n₂ => isFalse fun h => Prod.noConfusion h fun _   e₂' => absurd e₂' n₂
    | isFalse n₁ => isFalse fun h => Prod.noConfusion h fun e₁' _   => absurd e₁' n₁

instance [BEq α] [BEq β] : BEq (α × β) where
  beq := fun (a₁, b₁) (a₂, b₂) => a₁ == a₂ && b₁ == b₂

/-- Lexicographical order for products -/
def Prod.lexLt [LT α] [LT β] (s : α × β) (t : α × β) : Prop :=
  s.1 < t.1 ∨ (s.1 = t.1 ∧ s.2 < t.2)

instance Prod.lexLtDec
    [LT α] [LT β] [DecidableEq α] [DecidableEq β]
    [(a b : α) → Decidable (a < b)] [(a b : β) → Decidable (a < b)]
    : (s t : α × β) → Decidable (Prod.lexLt s t) :=
  fun _ _ => inferInstanceAs (Decidable (_ ∨ _))

theorem Prod.lexLt_def [LT α] [LT β] (s t : α × β) : (Prod.lexLt s t) = (s.1 < t.1 ∨ (s.1 = t.1 ∧ s.2 < t.2)) :=
  rfl

theorem Prod.eta (p : α × β) : (p.1, p.2) = p := rfl

/--
`Prod.map f g : α₁ × β₁ → α₂ × β₂` maps across a pair
by applying `f` to the first component and `g` to the second.
-/
def Prod.map {α₁ : Type u₁} {α₂ : Type u₂} {β₁ : Type v₁} {β₂ : Type v₂}
    (f : α₁ → α₂) (g : β₁ → β₂) : α₁ × β₁ → α₂ × β₂
  | (a, b) => (f a, g b)

/-! # Dependent products -/

theorem ex_of_PSigma {α : Type u} {p : α → Prop} : (PSigma (fun x => p x)) → Exists (fun x => p x)
  | ⟨x, hx⟩ => ⟨x, hx⟩

protected theorem PSigma.eta {α : Sort u} {β : α → Sort v} {a₁ a₂ : α} {b₁ : β a₁} {b₂ : β a₂}
    (h₁ : a₁ = a₂) (h₂ : Eq.ndrec b₁ h₁ = b₂) : PSigma.mk a₁ b₁ = PSigma.mk a₂ b₂ := by
  subst h₁
  subst h₂
  exact rfl

/-! # Universe polymorphic unit -/

theorem PUnit.subsingleton (a b : PUnit) : a = b := by
  cases a; cases b; exact rfl

theorem PUnit.eq_punit (a : PUnit) : a = ⟨⟩ :=
  PUnit.subsingleton a ⟨⟩

instance : Subsingleton PUnit :=
  Subsingleton.intro PUnit.subsingleton

instance : Inhabited PUnit where
  default := ⟨⟩

instance : DecidableEq PUnit :=
  fun a b => isTrue (PUnit.subsingleton a b)

/-! # Setoid -/

/--
A setoid is a type with a distinguished equivalence relation, denoted `≈`.
This is mainly used as input to the `Quotient` type constructor.
-/
class Setoid (α : Sort u) where
  /-- `x ≈ y` is the distinguished equivalence relation of a setoid. -/
  r : α → α → Prop
  /-- The relation `x ≈ y` is an equivalence relation. -/
  iseqv : Equivalence r

instance {α : Sort u} [Setoid α] : HasEquiv α :=
  ⟨Setoid.r⟩

namespace Setoid

variable {α : Sort u} [Setoid α]

theorem refl (a : α) : a ≈ a :=
  iseqv.refl a

theorem symm {a b : α} (hab : a ≈ b) : b ≈ a :=
  iseqv.symm hab

theorem trans {a b c : α} (hab : a ≈ b) (hbc : b ≈ c) : a ≈ c :=
  iseqv.trans hab hbc

end Setoid


/-! # Propositional extensionality -/

/--
The axiom of **propositional extensionality**. It asserts that if propositions
`a` and `b` are logically equivalent (i.e. we can prove `a` from `b` and vice versa),
then `a` and `b` are *equal*, meaning that we can replace `a` with `b` in all
contexts.

For simple expressions like `a ∧ c ∨ d → e` we can prove that because all the logical
connectives respect logical equivalence, we can replace `a` with `b` in this expression
without using `propext`. However, for higher order expressions like `P a` where
`P : Prop → Prop` is unknown, or indeed for `a = b` itself, we cannot replace `a` with `b`
without an axiom which says exactly this.

This is a relatively uncontroversial axiom, which is intuitionistically valid.
It does however block computation when using `#reduce` to reduce proofs directly
(which is not recommended), meaning that canonicity,
the property that all closed terms of type `Nat` normalize to numerals,
fails to hold when this (or any) axiom is used:
```
set_option pp.proofs true

def foo : Nat := by
  have : (True → True) ↔ True := ⟨λ _ => trivial, λ _ _ => trivial⟩
  have := propext this ▸ (2 : Nat)
  exact this

#reduce foo
-- propext { mp := fun x x => True.intro, mpr := fun x => True.intro } ▸ 2

#eval foo -- 2
```
`#eval` can evaluate it to a numeral because the compiler erases casts and
does not evaluate proofs, so `propext`, whose return type is a proposition,
can never block it.
-/
axiom propext {a b : Prop} : (a ↔ b) → a = b

theorem Eq.propIntro {a b : Prop} (h₁ : a → b) (h₂ : b → a) : a = b :=
  propext <| Iff.intro h₁ h₂

-- Eq for Prop is now decidable if the equivalent Iff is decidable
instance {p q : Prop} [d : Decidable (p ↔ q)] : Decidable (p = q) :=
  match d with
  | isTrue h => isTrue (propext h)
  | isFalse h => isFalse fun heq => h (heq ▸ Iff.rfl)

gen_injective_theorems% Prod
gen_injective_theorems% PProd
gen_injective_theorems% MProd
gen_injective_theorems% Subtype
gen_injective_theorems% Fin
gen_injective_theorems% Array
gen_injective_theorems% Sum
gen_injective_theorems% PSum
gen_injective_theorems% Nat
gen_injective_theorems% Option
gen_injective_theorems% List
gen_injective_theorems% Except
gen_injective_theorems% EStateM.Result
gen_injective_theorems% Lean.Name
gen_injective_theorems% Lean.Syntax

@[simp] theorem beq_iff_eq [BEq α] [LawfulBEq α] (a b : α) : a == b ↔ a = b :=
  ⟨eq_of_beq, by intro h; subst h; exact LawfulBEq.rfl⟩

/-! # Quotients -/

/-- Iff can now be used to do substitutions in a calculation -/
theorem Iff.subst {a b : Prop} {p : Prop → Prop} (h₁ : a ↔ b) (h₂ : p a) : p b :=
  Eq.subst (propext h₁) h₂

namespace Quot
/--
The **quotient axiom**, or at least the nontrivial part of the quotient
axiomatization. Quotient types are introduced by the `init_quot` command
in `Init.Prelude` which introduces the axioms:

```
opaque Quot {α : Sort u} (r : α → α → Prop) : Sort u

opaque Quot.mk {α : Sort u} (r : α → α → Prop) (a : α) : Quot r

opaque Quot.lift {α : Sort u} {r : α → α → Prop} {β : Sort v} (f : α → β) :
  (∀ a b : α, r a b → f a = f b) → Quot r → β

opaque Quot.ind {α : Sort u} {r : α → α → Prop} {β : Quot r → Prop} :
  (∀ a : α, β (Quot.mk r a)) → ∀ q : Quot r, β q
```
All of these axioms are true if we assume `Quot α r = α` and `Quot.mk` and
`Quot.lift` are identity functions, so they do not add much. However this axiom
cannot be explained in that way (it is false for that interpretation), so the
real power of quotient types come from this axiom.

It says that the quotient by `r` maps elements which are related by `r` to equal
values in the quotient. Together with `Quot.lift` which says that functions
which respect `r` can be lifted to functions on the quotient, we can deduce that
`Quot α r` exactly consists of the equivalence classes with respect to `r`.

It is important to note that `r` need not be an equivalence relation in this axiom.
When `r` is not an equivalence relation, we are actually taking a quotient with
respect to the equivalence relation generated by `r`.
-/
axiom sound : ∀ {α : Sort u} {r : α → α → Prop} {a b : α}, r a b → Quot.mk r a = Quot.mk r b

protected theorem liftBeta {α : Sort u} {r : α → α → Prop} {β : Sort v}
    (f : α → β)
    (c : (a b : α) → r a b → f a = f b)
    (a : α)
    : lift f c (Quot.mk r a) = f a :=
  rfl

protected theorem indBeta {α : Sort u} {r : α → α → Prop} {motive : Quot r → Prop}
    (p : (a : α) → motive (Quot.mk r a))
    (a : α)
    : (ind p (Quot.mk r a) : motive (Quot.mk r a)) = p a :=
  rfl

/--
`Quot.liftOn q f h` is the same as `Quot.lift f h q`. It just reorders
the argument `q : Quot r` to be first.
-/
protected abbrev liftOn {α : Sort u} {β : Sort v} {r : α → α → Prop}
  (q : Quot r) (f : α → β) (c : (a b : α) → r a b → f a = f b) : β :=
  lift f c q

@[elab_as_elim]
protected theorem inductionOn {α : Sort u} {r : α → α → Prop} {motive : Quot r → Prop}
    (q : Quot r)
    (h : (a : α) → motive (Quot.mk r a))
    : motive q :=
  ind h q

theorem exists_rep {α : Sort u} {r : α → α → Prop} (q : Quot r) : Exists (fun a => (Quot.mk r a) = q) :=
  q.inductionOn (fun a => ⟨a, rfl⟩)

section
variable {α : Sort u}
variable {r : α → α → Prop}
variable {motive : Quot r → Sort v}

/-- Auxiliary definition for `Quot.rec`. -/
@[reducible, macro_inline]
protected def indep (f : (a : α) → motive (Quot.mk r a)) (a : α) : PSigma motive :=
  ⟨Quot.mk r a, f a⟩

protected theorem indepCoherent
    (f : (a : α) → motive (Quot.mk r a))
    (h : (a b : α) → (p : r a b) → Eq.ndrec (f a) (sound p) = f b)
    : (a b : α) → r a b → Quot.indep f a = Quot.indep f b  :=
  fun a b e => PSigma.eta (sound e) (h a b e)

protected theorem liftIndepPr1
    (f : (a : α) → motive (Quot.mk r a))
    (h : ∀ (a b : α) (p : r a b), Eq.ndrec (f a) (sound p) = f b)
    (q : Quot r)
    : (lift (Quot.indep f) (Quot.indepCoherent f h) q).1 = q := by
 induction q using Quot.ind
 exact rfl

/--
Dependent recursion principle for `Quot`. This constructor can be tricky to use,
so you should consider the simpler versions if they apply:
* `Quot.lift`, for nondependent functions
* `Quot.ind`, for theorems / proofs of propositions about quotients
* `Quot.recOnSubsingleton`, when the target type is a `Subsingleton`
* `Quot.hrecOn`, which uses `HEq (f a) (f b)` instead of a `sound p ▸ f a = f b` assummption
-/
protected abbrev rec
    (f : (a : α) → motive (Quot.mk r a))
    (h : (a b : α) → (p : r a b) → Eq.ndrec (f a) (sound p) = f b)
    (q : Quot r) : motive q :=
  Eq.ndrecOn (Quot.liftIndepPr1 f h q) ((lift (Quot.indep f) (Quot.indepCoherent f h) q).2)

@[inherit_doc Quot.rec] protected abbrev recOn
    (q : Quot r)
    (f : (a : α) → motive (Quot.mk r a))
    (h : (a b : α) → (p : r a b) → Eq.ndrec (f a) (sound p) = f b)
    : motive q :=
 q.rec f h

/--
Dependent induction principle for a quotient, when the target type is a `Subsingleton`.
In this case the quotient's side condition is trivial so any function can be lifted.
-/
protected abbrev recOnSubsingleton
    [h : (a : α) → Subsingleton (motive (Quot.mk r a))]
    (q : Quot r)
    (f : (a : α) → motive (Quot.mk r a))
    : motive q := by
  induction q using Quot.rec
  apply f
  apply Subsingleton.elim

/--
Heterogeneous dependent recursion principle for a quotient.
This may be easier to work with since it uses `HEq` instead of
an `Eq.ndrec` in the hypothesis.
-/
protected abbrev hrecOn
    (q : Quot r)
    (f : (a : α) → motive (Quot.mk r a))
    (c : (a b : α) → (p : r a b) → HEq (f a) (f b))
    : motive q :=
  Quot.recOn q f fun a b p => eq_of_heq <|
    have p₁ : HEq (Eq.ndrec (f a) (sound p)) (f a) := eqRec_heq (sound p) (f a)
    HEq.trans p₁ (c a b p)

end
end Quot

set_option linter.unusedVariables.funArgs false in
/--
`Quotient α s` is the same as `Quot α r`, but it is specialized to a setoid `s`
(that is, an equivalence relation) instead of an arbitrary relation.
Prefer `Quotient` over `Quot` if your relation is actually an equivalence relation.
-/
def Quotient {α : Sort u} (s : Setoid α) :=
  @Quot α Setoid.r

namespace Quotient

/-- The canonical quotient map into a `Quotient`. -/
@[inline]
protected def mk {α : Sort u} (s : Setoid α) (a : α) : Quotient s :=
  Quot.mk Setoid.r a

/--
The canonical quotient map into a `Quotient`.
(This synthesizes the setoid by typeclass inference.)
-/
protected def mk' {α : Sort u} [s : Setoid α] (a : α) : Quotient s :=
  Quotient.mk s a

/--
The analogue of `Quot.sound`: If `a` and `b` are related by the equivalence relation,
then they have equal equivalence classes.
-/
def sound {α : Sort u} {s : Setoid α} {a b : α} : a ≈ b → Quotient.mk s a = Quotient.mk s b :=
  Quot.sound

/--
The analogue of `Quot.lift`: if `f : α → β` respects the equivalence relation `≈`,
then it lifts to a function on `Quotient s` such that `lift f h (mk a) = f a`.
-/
protected abbrev lift {α : Sort u} {β : Sort v} {s : Setoid α} (f : α → β) : ((a b : α) → a ≈ b → f a = f b) → Quotient s → β :=
  Quot.lift f

/-- The analogue of `Quot.ind`: every element of `Quotient s` is of the form `Quotient.mk s a`. -/
protected theorem ind {α : Sort u} {s : Setoid α} {motive : Quotient s → Prop} : ((a : α) → motive (Quotient.mk s a)) → (q : Quotient s) → motive q :=
  Quot.ind

/--
The analogue of `Quot.liftOn`: if `f : α → β` respects the equivalence relation `≈`,
then it lifts to a function on `Quotient s` such that `lift (mk a) f h = f a`.
-/
protected abbrev liftOn {α : Sort u} {β : Sort v} {s : Setoid α} (q : Quotient s) (f : α → β) (c : (a b : α) → a ≈ b → f a = f b) : β :=
  Quot.liftOn q f c

/-- The analogue of `Quot.inductionOn`: every element of `Quotient s` is of the form `Quotient.mk s a`. -/
@[elab_as_elim]
protected theorem inductionOn {α : Sort u} {s : Setoid α} {motive : Quotient s → Prop}
    (q : Quotient s)
    (h : (a : α) → motive (Quotient.mk s a))
    : motive q :=
  Quot.inductionOn q h

theorem exists_rep {α : Sort u} {s : Setoid α} (q : Quotient s) : Exists (fun (a : α) => Quotient.mk s a = q) :=
  Quot.exists_rep q

section
variable {α : Sort u}
variable {s : Setoid α}
variable {motive : Quotient s → Sort v}

/-- The analogue of `Quot.rec` for `Quotient`. See `Quot.rec`. -/
@[inline, elab_as_elim]
protected def rec
    (f : (a : α) → motive (Quotient.mk s a))
    (h : (a b : α) → (p : a ≈ b) → Eq.ndrec (f a) (Quotient.sound p) = f b)
    (q : Quotient s)
    : motive q :=
  Quot.rec f h q

/-- The analogue of `Quot.recOn` for `Quotient`. See `Quot.recOn`. -/
@[elab_as_elim]
protected abbrev recOn
    (q : Quotient s)
    (f : (a : α) → motive (Quotient.mk s a))
    (h : (a b : α) → (p : a ≈ b) → Eq.ndrec (f a) (Quotient.sound p) = f b)
    : motive q :=
  Quot.recOn q f h

/-- The analogue of `Quot.recOnSubsingleton` for `Quotient`. See `Quot.recOnSubsingleton`. -/
@[elab_as_elim]
protected abbrev recOnSubsingleton
    [h : (a : α) → Subsingleton (motive (Quotient.mk s a))]
    (q : Quotient s)
    (f : (a : α) → motive (Quotient.mk s a))
    : motive q :=
  Quot.recOnSubsingleton (h := h) q f

/-- The analogue of `Quot.hrecOn` for `Quotient`. See `Quot.hrecOn`. -/
@[elab_as_elim]
protected abbrev hrecOn
    (q : Quotient s)
    (f : (a : α) → motive (Quotient.mk s a))
    (c : (a b : α) → (p : a ≈ b) → HEq (f a) (f b))
    : motive q :=
  Quot.hrecOn q f c
end

section
universe uA uB uC
variable {α : Sort uA} {β : Sort uB} {φ : Sort uC}
variable {s₁ : Setoid α} {s₂ : Setoid β}

/-- Lift a binary function to a quotient on both arguments. -/
protected abbrev lift₂
    (f : α → β → φ)
    (c : (a₁ : α) → (b₁ : β) → (a₂ : α) → (b₂ : β) → a₁ ≈ a₂ → b₁ ≈ b₂ → f a₁ b₁ = f a₂ b₂)
    (q₁ : Quotient s₁) (q₂ : Quotient s₂)
    : φ := by
  apply Quotient.lift (fun (a₁ : α) => Quotient.lift (f a₁) (fun (a b : β) => c a₁ a a₁ b (Setoid.refl a₁)) q₂) _ q₁
  intros
  induction q₂ using Quotient.ind
  apply c; assumption; apply Setoid.refl

/-- Lift a binary function to a quotient on both arguments. -/
protected abbrev liftOn₂
    (q₁ : Quotient s₁)
    (q₂ : Quotient s₂)
    (f : α → β → φ)
    (c : (a₁ : α) → (b₁ : β) → (a₂ : α) → (b₂ : β) → a₁ ≈ a₂ → b₁ ≈ b₂ → f a₁ b₁ = f a₂ b₂)
    : φ :=
  Quotient.lift₂ f c q₁ q₂

@[elab_as_elim]
protected theorem ind₂
    {motive : Quotient s₁ → Quotient s₂ → Prop}
    (h : (a : α) → (b : β) → motive (Quotient.mk s₁ a) (Quotient.mk s₂ b))
    (q₁ : Quotient s₁)
    (q₂ : Quotient s₂)
    : motive q₁ q₂ := by
  induction q₁ using Quotient.ind
  induction q₂ using Quotient.ind
  apply h

@[elab_as_elim]
protected theorem inductionOn₂
    {motive : Quotient s₁ → Quotient s₂ → Prop}
    (q₁ : Quotient s₁)
    (q₂ : Quotient s₂)
    (h : (a : α) → (b : β) → motive (Quotient.mk s₁ a) (Quotient.mk s₂ b))
    : motive q₁ q₂ := by
  induction q₁ using Quotient.ind
  induction q₂ using Quotient.ind
  apply h

@[elab_as_elim]
protected theorem inductionOn₃
    {s₃ : Setoid φ}
    {motive : Quotient s₁ → Quotient s₂ → Quotient s₃ → Prop}
    (q₁ : Quotient s₁)
    (q₂ : Quotient s₂)
    (q₃ : Quotient s₃)
    (h : (a : α) → (b : β) → (c : φ) → motive (Quotient.mk s₁ a) (Quotient.mk s₂ b) (Quotient.mk s₃ c))
    : motive q₁ q₂ q₃ := by
  induction q₁ using Quotient.ind
  induction q₂ using Quotient.ind
  induction q₃ using Quotient.ind
  apply h

end

section Exact

variable {α : Sort u}

private def rel {s : Setoid α} (q₁ q₂ : Quotient s) : Prop :=
  Quotient.liftOn₂ q₁ q₂
    (fun a₁ a₂ => a₁ ≈ a₂)
    (fun _ _ _ _ a₁b₁ a₂b₂ =>
      propext (Iff.intro
        (fun a₁a₂ => Setoid.trans (Setoid.symm a₁b₁) (Setoid.trans a₁a₂ a₂b₂))
        (fun b₁b₂ => Setoid.trans a₁b₁ (Setoid.trans b₁b₂ (Setoid.symm a₂b₂)))))

private theorem rel.refl {s : Setoid α} (q : Quotient s) : rel q q :=
  q.inductionOn Setoid.refl

private theorem rel_of_eq {s : Setoid α} {q₁ q₂ : Quotient s} : q₁ = q₂ → rel q₁ q₂ :=
  fun h => Eq.ndrecOn h (rel.refl q₁)

theorem exact {s : Setoid α} {a b : α} : Quotient.mk s a = Quotient.mk s b → a ≈ b :=
  fun h => rel_of_eq h

end Exact

section
universe uA uB uC
variable {α : Sort uA} {β : Sort uB}
variable {s₁ : Setoid α} {s₂ : Setoid β}

/-- Lift a binary function to a quotient on both arguments. -/
@[elab_as_elim]
protected abbrev recOnSubsingleton₂
    {motive : Quotient s₁ → Quotient s₂ → Sort uC}
    [s : (a : α) → (b : β) → Subsingleton (motive (Quotient.mk s₁ a) (Quotient.mk s₂ b))]
    (q₁ : Quotient s₁)
    (q₂ : Quotient s₂)
    (g : (a : α) → (b : β) → motive (Quotient.mk s₁ a) (Quotient.mk s₂ b))
    : motive q₁ q₂ := by
  induction q₁ using Quot.recOnSubsingleton
  induction q₂ using Quot.recOnSubsingleton
  apply g
  intro a; apply s
  induction q₂ using Quot.recOnSubsingleton
  intro a; apply s
  infer_instance

end
end Quotient

section
variable {α : Type u}
variable (r : α → α → Prop)

instance {α : Sort u} {s : Setoid α} [d : ∀ (a b : α), Decidable (a ≈ b)] : DecidableEq (Quotient s) :=
  fun (q₁ q₂ : Quotient s) =>
    Quotient.recOnSubsingleton₂ q₁ q₂
      fun a₁ a₂ =>
        match d a₁ a₂ with
        | isTrue h₁  => isTrue (Quotient.sound h₁)
        | isFalse h₂ => isFalse fun h => absurd (Quotient.exact h) h₂

/-! # Function extensionality -/

/--
**Function extensionality** is the statement that if two functions take equal values
every point, then the functions themselves are equal: `(∀ x, f x = g x) → f = g`.
It is called "extensionality" because it talks about how to prove two objects are equal
based on the properties of the object (compare with set extensionality,
which is `(∀ x, x ∈ s ↔ x ∈ t) → s = t`).

This is often an axiom in dependent type theory systems, because it cannot be proved
from the core logic alone. However in lean's type theory this follows from the existence
of quotient types (note the `Quot.sound` in the proof, as well as the `show` line
which makes use of the definitional equality `Quot.lift f h (Quot.mk x) = f x`).
-/
theorem funext {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}
    (h : ∀ x, f x = g x) : f = g := by
  let eqv (f g : (x : α) → β x) := ∀ x, f x = g x
  let extfunApp (f : Quot eqv) (x : α) : β x :=
    Quot.liftOn f
      (fun (f : ∀ (x : α), β x) => f x)
      (fun _ _ h => h x)
  show extfunApp (Quot.mk eqv f) = extfunApp (Quot.mk eqv g)
  exact congrArg extfunApp (Quot.sound h)

instance {α : Sort u} {β : α → Sort v} [∀ a, Subsingleton (β a)] : Subsingleton (∀ a, β a) where
  allEq f g := funext fun a => Subsingleton.elim (f a) (g a)

/-! # Squash -/

/--
`Squash α` is the quotient of `α` by the always true relation.
It is empty if `α` is empty, otherwise it is a singleton.
(Thus it is unconditionally a `Subsingleton`.)
It is the "universal `Subsingleton`" mapped from `α`.

It is similar to `Nonempty α`, which has the same properties, but unlike
`Nonempty` this is a `Type u`, that is, it is "data", and the compiler
represents an element of `Squash α` the same as `α` itself
(as compared to `Nonempty α`, whose elements are represented by a dummy value).

`Squash.lift` will extract a value in any subsingleton `β` from a function on `α`,
while `Nonempty.rec` can only do the same when `β` is a proposition.
-/
def Squash (α : Type u) := Quot (fun (_ _ : α) => True)

/-- The canonical quotient map into `Squash α`. -/
def Squash.mk {α : Type u} (x : α) : Squash α := Quot.mk _ x

theorem Squash.ind {α : Type u} {motive : Squash α → Prop} (h : ∀ (a : α), motive (Squash.mk a)) : ∀ (q : Squash α), motive q :=
  Quot.ind h

/-- If `β` is a subsingleton, then a function `α → β` lifts to `Squash α → β`. -/
@[inline] def Squash.lift {α β} [Subsingleton β] (s : Squash α) (f : α → β) : β :=
  Quot.lift f (fun _ _ _ => Subsingleton.elim _ _) s

instance : Subsingleton (Squash α) where
  allEq a b := by
    induction a using Squash.ind
    induction b using Squash.ind
    apply Quot.sound
    trivial

/-! # Relations -/

/--
`Antisymm (·≤·)` says that `(·≤·)` is antisymmetric, that is, `a ≤ b → b ≤ a → a = b`.
-/
class Antisymm {α : Sort u} (r : α → α → Prop) where
  /-- An antisymmetric relation `(·≤·)` satisfies `a ≤ b → b ≤ a → a = b`. -/
  antisymm {a b : α} : r a b → r b a → a = b

namespace Lean
/-! # Kernel reduction hints -/

/--
Depends on the correctness of the Lean compiler, interpreter, and all `[implemented_by ...]` and `[extern ...]` annotations.
-/
axiom trustCompiler : True

/--
When the kernel tries to reduce a term `Lean.reduceBool c`, it will invoke the Lean interpreter to evaluate `c`.
The kernel will not use the interpreter if `c` is not a constant.
This feature is useful for performing proofs by reflection.

Remark: the Lean frontend allows terms of the from `Lean.reduceBool t` where `t` is a term not containing
free variables. The frontend automatically declares a fresh auxiliary constant `c` and replaces the term with
`Lean.reduceBool c`. The main motivation is that the code for `t` will be pre-compiled.

Warning: by using this feature, the Lean compiler and interpreter become part of your trusted code base.
This is extra 30k lines of code. More importantly, you will probably not be able to check your development using
external type checkers (e.g., Trepplein) that do not implement this feature.
Keep in mind that if you are using Lean as programming language, you are already trusting the Lean compiler and interpreter.
So, you are mainly losing the capability of type checking your development using external checkers.

Recall that the compiler trusts the correctness of all `[implemented_by ...]` and `[extern ...]` annotations.
If an extern function is executed, then the trusted code base will also include the implementation of the associated
foreign function.
-/
opaque reduceBool (b : Bool) : Bool :=
  -- This ensures that `#print axioms` will track use of `reduceBool`.
  have := trustCompiler
  b

/--
Similar to `Lean.reduceBool` for closed `Nat` terms.

Remark: we do not have plans for supporting a generic `reduceValue {α} (a : α) : α := a`.
The main issue is that it is non-trivial to convert an arbitrary runtime object back into a Lean expression.
We believe `Lean.reduceBool` enables most interesting applications (e.g., proof by reflection).
-/
opaque reduceNat (n : Nat) : Nat :=
  -- This ensures that `#print axioms` will track use of `reduceNat`.
  have := trustCompiler
  n


/--
The axiom `ofReduceBool` is used to perform proofs by reflection. See `reduceBool`.

This axiom is usually not used directly, because it has some syntactic restrictions.
Instead, the `native_decide` tactic can be used to prove any proposition whose
decidability instance can be evaluated to `true` using the lean compiler / interpreter.

Warning: by using this feature, the Lean compiler and interpreter become part of your trusted code base.
This is extra 30k lines of code. More importantly, you will probably not be able to check your development using
external type checkers (e.g., Trepplein) that do not implement this feature.
Keep in mind that if you are using Lean as programming language, you are already trusting the Lean compiler and interpreter.
So, you are mainly losing the capability of type checking your development using external checkers.
-/
axiom ofReduceBool (a b : Bool) (h : reduceBool a = b) : a = b

/--
The axiom `ofReduceNat` is used to perform proofs by reflection. See `reduceBool`.

Warning: by using this feature, the Lean compiler and interpreter become part of your trusted code base.
This is extra 30k lines of code. More importantly, you will probably not be able to check your development using
external type checkers (e.g., Trepplein) that do not implement this feature.
Keep in mind that if you are using Lean as programming language, you are already trusting the Lean compiler and interpreter.
So, you are mainly losing the capability of type checking your development using external checkers.
-/
axiom ofReduceNat (a b : Nat) (h : reduceNat a = b) : a = b

/--
`IsAssociative op` says that `op` is an associative operation,
i.e. `(a ∘ b) ∘ c = a ∘ (b ∘ c)`. It is used by the `ac_rfl` tactic.
-/
class IsAssociative {α : Sort u} (op : α → α → α) where
  /-- An associative operation satisfies `(a ∘ b) ∘ c = a ∘ (b ∘ c)`. -/
  assoc : (a b c : α) → op (op a b) c = op a (op b c)

/--
`IsCommutative op` says that `op` is a commutative operation,
i.e. `a ∘ b = b ∘ a`. It is used by the `ac_rfl` tactic.
-/
class IsCommutative {α : Sort u} (op : α → α → α) where
  /-- A commutative operation satisfies `a ∘ b = b ∘ a`. -/
  comm : (a b : α) → op a b = op b a

/--
`IsIdempotent op` says that `op` is an idempotent operation,
i.e. `a ∘ a = a`. It is used by the `ac_rfl` tactic
(which also simplifies up to idempotence when available).
-/
class IsIdempotent {α : Sort u} (op : α → α → α) where
  /-- An idempotent operation satisfies `a ∘ a = a`. -/
  idempotent : (x : α) → op x x = x

/--
`IsNeutral op e` says that `e` is a neutral operation for `op`,
i.e. `a ∘ e = a = e ∘ a`. It is used by the `ac_rfl` tactic
(which also simplifies neutral elements when available).
-/
class IsNeutral {α : Sort u} (op : α → α → α) (neutral : α) where
  /-- A neutral element can be cancelled on the left: `e ∘ a = a`. -/
  left_neutral : (a : α) → op neutral a = a
  /-- A neutral element can be cancelled on the right: `a ∘ e = a`. -/
  right_neutral : (a : α) → op a neutral = a

end Lean

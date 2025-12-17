/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Init.Control.Basic

set_option linter.all true

set_option doc.verso true

/-!
# {name (scope := "Init.Control.MonadAttach")}`MonadAttach`

This module provides a mechanism for attaching proofs to the return values of monadic computations,
producing a new monadic computation returning a {name}`Subtype`.

This function is primarily used to allow definitions by [well-founded
recursion](lean-manual://section/well-founded-recursion) that sequence computations using
{name}`Bind.bind` (`>>=`) to prove properties about the return values of prior computations when
a recursive call happens.
This allows the well-founded recursion mechanism to prove that the function terminates.
-/

-- verso docstring is added below
set_option linter.missingDocs false in
public class MonadAttach (m : Type u → Type v) where
  /--
  A predicate that can be assumed to be true for all return values {name}`a` of actions {name}`x`
  in {name}`m`, in all situations.
  -/
  CanReturn {α : Type u} : (x : m α) → (a : α) → Prop
  /--
  Attaches a proof of {name}`MonadAttach.CanReturn` to the return value of {name}`x`. This proof
  can be used to prove the termination of well-founded recursive functions.
  -/
  attach {α : Type u} (x : m α) : m (Subtype (CanReturn x))

-- verso docstring is added below
set_option linter.missingDocs false in
public class WeaklyLawfulMonadAttach (m : Type u → Type v) [Monad m] [MonadAttach m] where
  map_attach {α : Type u} {x : m α} : Subtype.val <$> MonadAttach.attach x = x

/--
This type class ensures that {name}`MonadAttach.CanReturn` is the unique strongest possible
postcondition.
-/
public class LawfulMonadAttach (m : Type u → Type v) [Monad m] [MonadAttach m] extends
    WeaklyLawfulMonadAttach m where
  canReturn_map_imp {α : Type u} {P : α → Prop} {x : m (Subtype P)} {a : α} :
      MonadAttach.CanReturn (Subtype.val <$> x) a → P a

/--
Like {name}`Bind.bind`, {name}`pbind` sequences two computations {lean}`x : m α` and {lean}`f`,
allowing the second to depend on the value computed by the first.
But other than with {name}`Bind.bind`, the second computation can also depend on a proof that
the return value {given}`a` of {name}`x` satisfies {lean}`MonadAttach.CanReturn x a`.
-/
public def MonadAttach.pbind [Monad m] [MonadAttach m]
    (x : m α) (f : (a : α) → MonadAttach.CanReturn x a → m β) : m β :=
  MonadAttach.attach x >>= (fun ⟨a, ha⟩ => f a ha)

/--
A {lean}`MonadAttach` instance where all return values are possible and {name}`attach` adds no
information to the return value, except a trivial proof of {name}`True`.

This instance is used whenever no more useful {name}`MonadAttach` instance can be implemented.
It always has a {name}`WeaklyLawfulMonadAttach`, but usually no {name}`LawfulMonadAttach` instance.
-/
@[expose]
public protected def MonadAttach.trivial {m : Type u → Type v} [Monad m] : MonadAttach m where
  CanReturn _ _ := True
  attach x := (⟨·, .intro⟩) <$> x

section

variable (α : Type u) [∀ m, Monad m] [∀ m, MonadAttach m]

set_option doc.verso true

/--
For every {given}`x : m α`, this type class provides a predicate {lean}`MonadAttach.CanReturn x`
and a way to attach a proof of this predicate to the return values of {name}`x` by providing
an element {lean}`MonadAttach.attach x` of {lean}`m { a : α // MonadAttach.CanReturn x a }`.

Instances should abide the law {lean}`Subtype.val <$> MonadAttach.attach x = x`, which is encoded by
the {name}`WeaklyLawfulMonadAttach` type class. The stronger type class {name}`LawfulMonadAttach`
ensures that {lean}`MonadAttach.CanReturn x` is the _unique_ strongest possible predicate.

Similarly to {name (scope := "Init.Data.List.Attach")}`List.attach`, the purpose of
{name}`MonadAttach` is to attach proof terms necessary for well-founded termination proofs.
The iterator library relies on {name}`MonadAttach` for combinators such as
{name (scope := "Init.Data.Iterators")}`Std.Iter.filterM` in order to automatically attach
information about the monadic predicate's behavior that could be relevant for the termination
behavior of the iterator.

*Limitations*:

For many monads, there is a strongly lawful {lean}`MonadAttach` instance, but there are exceptions.
For example, there is no way to provide a computable {lean}`MonadAttach` instance for the CPS monad
transformers
{name (scope := "Init.Control.StateCps")}`StateCpsT` and
{name (scope := "Init.Control.StateCps")}`ExceptCpsT` with a predicate that is not always
{name}`True`. Therefore, such CPS monads only provide the trivial {lean}`MonadAttach` instance
{lean}`MonadAttach.trivial` together with {name}`WeaklyLawfulMonadAttach`, but without
{name}`LawfulMonadAttach`.

For most monads with side effects, {lean}`MonadAttach` is too weak to fully capture the behavior of
computations because the postcondition represented by {name}`MonadAttach.CanReturn` neither depends
on the prior internal state of the monad, nor does it contain information about how the state of the
monad changes with the computation.
-/
add_decl_doc MonadAttach

/--
This type class ensures that every monadic action {given}`x : m α` can be recovered by stripping the
proof component from the subtypes returned by
{lean}`(MonadAttach.attach x) : m { a : α // MonadAttach.CanReturn x a }` . In other words,
the type class ensures that {lean}`Subtype.val <$> MonadAttach.attach x = x`.
-/
add_decl_doc WeaklyLawfulMonadAttach

end

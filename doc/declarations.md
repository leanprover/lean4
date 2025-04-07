# Declarations

-- TODO (fix)

Declaration Names
=================

A declaration name is a hierarchical [identifier](lexical_structure.md#identifiers) that is interpreted relative to the current namespace as well as (during lookup) to the set of open namespaces.

```lean
namespace A
  opaque B.c : Nat
  #print B.c -- opaque A.B.c : Nat
end A

#print A.B.c -- opaque A.B.c : Nat
open A
#print B.c -- opaque A.B.c : Nat
```

Declaration names starting with an underscore are reserved for internal use. Names starting with the special atomic name ``_root_`` are interpreted as absolute names.

```lean
opaque a : Nat
namespace A
  opaque a : Int
  #print _root_.a -- opaque a : Nat
  #print A.a      -- opaque A.a : Int
end A
```

Contexts and Telescopes
=======================

When processing user input, Lean first parses text to a raw expression format. It then uses background information and type constants to disambiguate overloaded symbols and infer implicit arguments, resulting in a fully-formed expression. This process is known as *elaboration*.

As hinted in [Expression Syntax](expressions.md#expression_syntax),
expressions are parsed and elaborated with respect to an *environment*
and a *local context*. Roughly speaking, an environment represents the
state of Lean at the point where an expression is parsed, including
previously declared axioms, constants, definitions, and theorems. In a
given environment, a *local context* consists of a sequence ``(a₁ :
α₁) (a₂ : α₂) ... (aₙ : αₙ)`` where each ``aᵢ`` is a name denoting a
local constant and each ``αᵢ`` is an expression of type ``Sort u`` for
some ``u`` which can involve elements of the environment and the local
constants ``aⱼ`` for ``j < i``.

Intuitively, a local context is a list of variables that are held constant while an expression is being elaborated. Consider the following

```lean
def f (a b : Nat) : Nat → Nat := fun c => a + (b + c)
```

Here the expression ``fun c => a + (b + c)`` is elaborated in the context ``(a : Nat) (b : Nat)`` and the expression ``a + (b + c)`` is elaborated in the context ``(a : Nat) (b : Nat) (c : Nat)``. If you replace the expression ``a + (b + c)`` with an underscore, the error message from Lean will include the current *goal*:

```
a b c : Nat
⊢ Nat
```

Here ``a b c : Nat`` indicates the local context, and the second ``Nat`` indicates the expected type of the result.

A *context* is sometimes called a *telescope*, but the latter is used more generally to include a sequence of declarations occurring relative to a given context. For example, relative to the context ``(a₁ : α₁) (a₂ : α₂) ... (aₙ : αₙ)``, the types ``βᵢ`` in a telescope ``(b₁ : β₁) (b₂ : β₂) ... (bₙ : βₙ)`` can refer to ``a₁, ..., aₙ``. Thus a context can be viewed as a telescope relative to the empty context.

Telescopes are often used to describe a list of arguments, or parameters, to a declaration. In such cases, it is often notationally convenient to let ``(a : α)`` stand for a telescope rather than just a single argument. In general, the annotations described in [Implicit Arguments](expressions.md#implicit_arguments) can be used to mark arguments as implicit.

.. _basic_declarations:

Basic Declarations
==================

Lean provides ways of adding new objects to the environment. The following provide straightforward ways of declaring new objects:

* ``axiom c : α`` :  declare a constant named ``c`` of type ``α``, it is postulating that `α` is not an empty type.
* ``def c : α := v`` : defines ``c`` to denote ``v``, which should have type ``α``.
* ``theorem c : p := v`` : similar to ``def``, but intended to be used when ``p`` is a proposition.
* ``opaque c : α (:= v)?`` : declares a opaque constant named ``c`` of type ``α``, the optional value `v` is must have type `α`
  and can be viewed as a certificate that ``α`` is not an empty type. If the value is not provided, Lean tries to find one
  using a procedure based on type class resolution. The value `v` is hidden from the type checker. You can assume that
  Lean "forgets" `v` after type checking this kind of declaration.

It is sometimes useful to be able to simulate a definition or theorem without naming it or adding it to the environment.

* ``example : α := t`` : elaborates ``t`` and checks that it has sort ``α`` (often a proposition), without adding it to the environment.

In ``def``, the type (``α`` or ``p``, respectively) can be omitted when it can be inferred by Lean. Constants declared with ``theorem`` are marked as ``irreducible``.

Any of ``def``, ``theorem``, ``axiom``, or ``example`` can take a list of arguments (that is, a context) before the colon. If ``(a : α)`` is a context, the definition ``def foo (a : α) : β := t``
is interpreted as ``def foo : (a : α) → β := fun a : α => t``. Similarly, a theorem ``theorem foo (a : α) : p := t`` is interpreted as ``theorem foo : ∀ a : α, p := fun a : α => t``.

```lean
opaque c : Nat
opaque d : Nat
axiom cd_eq : c = d

def foo : Nat := 5
def bar := 6
def baz (x y : Nat) (s : List Nat) := [x, y] ++ s

theorem foo_eq_five : foo = 5 := rfl
theorem baz_theorem (x y : Nat) : baz x y [] = [x, y] := rfl

example (x y : Nat) : baz x y [] = [x, y] := rfl
```

Inductive Types
===============

Lean's axiomatic foundation allows users to declare arbitrary
inductive families, following the pattern described by [Dybjer]_. To
make the presentation more manageable, we first describe inductive
*types*, and then describe the generalization to inductive *families*
in the next section. The declaration of an inductive type has the
following form:

```
inductive Foo (a : α) where
  | constructor₁ : (b : β₁) → Foo a
  | constructor₂ : (b : β₂) → Foo a
  ...
  | constructorₙ : (b : βₙ) → Foo a
```

Here ``(a : α)`` is a context and each ``(b : βᵢ)`` is a telescope in the context ``(a : α)`` together with ``Foo``, subject to the following constraints.

Suppose the telescope ``(b : βᵢ)`` is ``(b₁ : βᵢ₁) ... (bᵤ : βᵢᵤ)``. Each argument in the telescope is either *nonrecursive* or *recursive*.

- An argument ``(bⱼ : βᵢⱼ)`` is *nonrecursive* if ``βᵢⱼ`` does not refer to ``foo,`` the inductive type being defined. In that case, ``βᵢⱼ`` can be any type, so long as it does not refer to any nonrecursive arguments.

- An argument ``(bⱼ : βᵢⱼ)`` is *recursive* if it ``βᵢⱼ`` of the form ``Π (d : δ), foo`` where ``(d : δ)`` is a telescope which does not refer to ``foo`` or any nonrecursive arguments.

The inductive type ``foo`` represents a type that is freely generated by the constructors. Each constructor can take arbitrary data and facts as arguments (the nonrecursive arguments), as well as indexed sequences of elements of ``foo`` that have been previously constructed (the recursive arguments). In set theoretic models, such sets can be represented by well-founded trees labeled by the constructor data, or they can defined using other transfinite or impredicative means.

The declaration of the type ``foo`` as above results in the addition of the following constants to the environment:

- the *type former* ``foo : Π (a : α), Sort u``
- for each ``i``, the *constructor* ``foo.constructorᵢ : Π (a : α) (b : βᵢ), foo a``
- the *eliminator* ``foo.rec``, which takes arguments

  + ``(a : α)`` (the parameters)
  + ``{C : foo a → Type u}`` (the *motive* of the elimination)
  + for each ``i``, the *minor premise* corresponding to ``constructorᵢ``
  + ``(x : foo)`` (the *major premise*)

  and returns an element of ``C x``. Here, The ith minor premise is a function which takes

  +  ``(b : βᵢ)`` (the arguments to the constructor)
  + an argument of type ``Π (d : δ), C (bⱼ d)`` corresponding to each recursive argument ``(bⱼ : βᵢⱼ)``, where ``βᵢⱼ``  is of the form ``Π (d : δ), foo`` (the recursive values of the function being defined)

  and returns an element of ``C (constructorᵢ a b)``, the intended value of the function at ``constructorᵢ a b``.

The eliminator represents a principle of recursion: to construct an element of ``C x`` where ``x : foo a``, it suffices to consider each of the cases where ``x`` is of the form ``constructorᵢ a b`` and to provide an auxiliary construction in each case. In the case where some of the arguments to ``constructorᵢ`` are recursive, we can assume that we have already constructed values of ``C y`` for each value ``y`` constructed at an earlier stage.

Under the propositions-as-type correspondence, when ``C x`` is an element of ``Prop``, the eliminator represents a principle of induction. In order to show ``∀ x, C x``, it suffices to show that ``C`` holds for each constructor, under the inductive hypothesis that it holds for all recursive inputs to the constructor.

The eliminator and constructors satisfy the following identities, in which all the arguments are shown explicitly. Suppose we set ``F := foo.rec a C f₁ ... fₙ``. Then for each constructor, we have the definitional reduction:

```
F (constructorᵢ a b) = fᵢ b ... (fun d : δᵢⱼ => F (bⱼ d)) ...
```

where the ellipses include one entry for each recursive argument.

Below are some common examples of inductive types, many of which are defined in the core library.

```lean
namespace Hide
universe u v

-- BEGIN
inductive Empty : Type

inductive Unit : Type
| unit : Unit

inductive Bool : Type
| false : Bool
| true : Bool

inductive Prod (α : Type u) (β : Type v) : Type (max u v)
| mk : α → β → Prod α β

inductive Sum (α : Type u) (β : Type v)
| inl : α → Sum α β
| inr : β → Sum α β

inductive Sigma (α : Type u) (β : α → Type v)
| mk : (a : α) → β a → Sigma α β

inductive false : Prop

inductive True : Prop
| trivial : True

inductive And (p q : Prop) : Prop
| intro : p → q → And p q

inductive Or (p q : Prop) : Prop
| inl : p → Or p q
| inr : q → Or p q

inductive Exists (α : Type u) (p : α → Prop) : Prop
| intro : ∀ x : α, p x → Exists α p

inductive Subtype (α : Type u) (p : α → Prop) : Type u
| intro : ∀ x : α, p x → Subtype α p

inductive Nat : Type
| zero : Nat
| succ : Nat → Nat

inductive List (α : Type u)
| nil : List α
| cons : α → List α → List α

-- full binary tree with nodes and leaves labeled from α
inductive BinTree (α : Type u)
| leaf : α → BinTree α
| node : BinTree α → α → BinTree α → BinTree α

-- every internal node has subtrees indexed by Nat
inductive CBT (α : Type u)
| leaf : α → CBT α
| node : (Nat → CBT α) → CBT α
-- END
end Hide
```

Note that in the syntax of the inductive definition ``Foo``, the context ``(a : α)`` is left implicit. In other words, constructors and recursive arguments are written as though they have return type ``Foo`` rather than ``Foo a``.

Elements of the context ``(a : α)`` can be marked implicit as described in [Implicit Arguments](#implicit.md#implicit_arguments). These annotations bear only on the type former, ``Foo``. Lean uses a heuristic to determine which arguments to the constructors should be marked implicit, namely, an argument is marked implicit if it can be inferred from the type of a subsequent argument. If the annotation ``{}`` appears after the constructor, a argument is marked implicit if it can be inferred from the type of a subsequent argument *or the return type*. For example, it is useful to let ``nil`` denote the empty list of any type, since the type can usually be inferred in the context in which it appears. These heuristics are imperfect, and you may sometimes wish to define your own constructors in terms of the default ones. In that case, use the ``[match_pattern]`` [attribute](TODO: missing link) to ensure that these will be used appropriately by the [Equation Compiler](#the-equation-compiler).

There are restrictions on the universe ``u`` in the return type ``Sort u`` of the type former. There are also restrictions on the universe ``u`` in the return type ``Sort u`` of the motive of the eliminator. These will be discussed in the next section in the more general setting of inductive families.

Lean allows some additional syntactic conveniences. You can omit the return type of the type former, ``Sort u``, in which case Lean will infer the minimal possible nonzero value for ``u``. As with function definitions, you can list arguments to the constructors before the colon. In an enumerated type (that is, one where the constructors have no arguments), you can also leave out the return type of the constructors.

```lean
namespace Hide
universe u

-- BEGIN
inductive Weekday
| sunday | monday | tuesday | wednesday
| thursday | friday | saturday

inductive Nat
| zero
| succ (n : Nat) : Nat

inductive List (α : Type u)
| nil : List α
| cons (a : α) (l : List α) : List α

@[match_pattern]
def List.nil' (α : Type u) : List α := List.nil

def length {α : Type u} : List α → Nat
| (List.nil' _) => 0
| (List.cons a l) => 1 + length l
-- END

end Hide
```

The type former, constructors, and eliminator are all part of Lean's axiomatic foundation, which is to say, they are part of the trusted kernel. In addition to these axiomatically declared constants, Lean automatically defines some additional objects in terms of these, and adds them to the environment. These include the following:

- ``Foo.recOn`` : a variant of the eliminator, in which the major premise comes first
- ``Foo.casesOn`` : a restricted version of the eliminator which omits any recursive calls
- ``Foo.noConfusionType``, ``Foo.noConfusion`` : functions which witness the fact that the inductive type is freely generated, i.e. that the constructors are injective and that distinct constructors produce distinct objects
- ``Foo.below``, ``Foo.ibelow`` : functions used by the equation compiler to implement structural recursion
- ``instance : SizeOf Foo`` : a measure which can be used for well-founded recursion

Note that it is common to put definitions and theorems related to a datatype ``foo`` in a namespace of the same name. This makes it possible to use projection notation described in [Structures](struct.md#structures) and [Namespaces](namespaces.md#namespaces).

```lean
namespace Hide
universe u

-- BEGIN
inductive Nat
| zero
| succ (n : Nat) : Nat

#check Nat
#check @Nat.rec
#check Nat.zero
#check Nat.succ

#check @Nat.recOn
#check @Nat.casesOn
#check @Nat.noConfusionType
#check @Nat.noConfusion
#check @Nat.brecOn
#check Nat.below
#check Nat.ibelow
#check Nat._sizeOf_1

-- END

end Hide
```

.. _inductive_families:

Inductive Families
==================

In fact, Lean implements a slight generalization of the inductive types described in the previous section, namely, inductive *families*. The declaration of an inductive family in Lean has the following form:

```
inductive Foo (a : α) : Π (c : γ), Sort u
| constructor₁ : Π (b : β₁), Foo t₁
| constructor₂ : Π (b : β₂), Foo t₂
...
| constructorₙ : Π (b : βₙ), Foo tₙ
```

Here ``(a : α)`` is a context, ``(c : γ)`` is a telescope in context ``(a : α)``, each ``(b : βᵢ)`` is a telescope in the context ``(a : α)`` together with ``(Foo : Π (c : γ), Sort u)`` subject to the constraints below, and each ``tᵢ`` is a tuple of terms in the context ``(a : α) (b : βᵢ)`` having the types ``γ``. Instead of defining a single inductive type ``Foo a``, we are now defining a family of types ``Foo a c`` indexed by elements ``c : γ``.  Each constructor, ``constructorᵢ``, places its result in the type ``Foo a tᵢ``, the member of the family with index ``tᵢ``.

The modifications to the scheme in the previous section are straightforward. Suppose the telescope ``(b : βᵢ)`` is ``(b₁ : βᵢ₁) ... (bᵤ : βᵢᵤ)``.

- As before, an argument ``(bⱼ : βᵢⱼ)`` is *nonrecursive* if ``βᵢⱼ`` does not refer to ``Foo,`` the inductive type being defined. In that case, ``βᵢⱼ`` can be any type, so long as it does not refer to any nonrecursive arguments.

- An argument ``(bⱼ : βᵢⱼ)`` is *recursive* if ``βᵢⱼ`` is of the form ``Π (d : δ), Foo s`` where ``(d : δ)`` is a telescope which does not refer to ``Foo`` or any nonrecursive arguments and ``s`` is a tuple of terms in context ``(a : α)`` and the previous nonrecursive ``bⱼ``'s with types ``γ``.

The declaration of the type ``Foo`` as above results in the addition of the following constants to the environment:

- the *type former* ``Foo : Π (a : α) (c : γ), Sort u``
- for each ``i``, the *constructor* ``Foo.constructorᵢ : Π (a : α) (b : βᵢ), Foo a tᵢ``
- the *eliminator* ``Foo.rec``, which takes arguments

  + ``(a : α)`` (the parameters)
  + ``{C : Π (c : γ), Foo a c → Type u}`` (the motive of the elimination)
  + for each ``i``, the minor premise corresponding to ``constructorᵢ``
  + ``(x : Foo a)`` (the major premise)

  and returns an element of ``C x``. Here, The ith minor premise is a function which takes

  +  ``(b : βᵢ)`` (the arguments to the constructor)
  + an argument of type ``Π (d : δ), C s (bⱼ d)`` corresponding to each recursive argument ``(bⱼ : βᵢⱼ)``, where ``βᵢⱼ``  is of the form ``Π (d : δ), Foo s``

  and returns an element of ``C tᵢ (constructorᵢ a b)``.

Suppose we set ``F := Foo.rec a C f₁ ... fₙ``. Then for each constructor, we have the definitional reduction, as before:

```
F (constructorᵢ a b) = fᵢ b ... (fun d : δᵢⱼ => F (bⱼ d)) ...
```

where the ellipses include one entry for each recursive argument.

The following are examples of inductive families.

```lean
namespace Hide
universe u

-- BEGIN
inductive Vector (α : Type u) : Nat → Type u
| nil  : Vector 0
| succ : Π n, Vector n → Vector (n + 1)

-- 'IsProd s n' means n is a product of elements of s
inductive IsProd (s : Set Nat) : Nat → Prop
| base : ∀ n ∈ s, IsProd n
| step : ∀ m n, IsProd m → IsProd n → IsProd (m * n)

inductive Eq {α : Sort u} (a : α) : α → Prop
| refl : Eq a
-- END

end Hide
```

We can now describe the constraints on the return type of the type former, ``Sort u``. We can always take ``u`` to be ``0``, in which case we are defining an inductive family of propositions. If ``u`` is nonzero, however, it must satisfy the following constraint: for each type ``βᵢⱼ : Sort v`` occurring in the constructors, we must have ``u ≥ v``. In the set-theoretic interpretation, this ensures that the universe in which the resulting type resides is large enough to contain the inductively generated family, given the number of distinctly-labeled constructors. The restriction does not hold for inductively defined propositions, since these contain no data.

Putting an inductive family in ``Prop``, however, does impose a restriction on the eliminator. Generally speaking, for an inductive family in ``Prop``, the motive in the eliminator is required to be in ``Prop``. But there is an exception to this rule: you are allowed to eliminate from an inductively defined ``Prop`` to an arbitrary ``Sort`` when there is only one constructor, and each argument to that constructor is either in ``Prop`` or an index. The intuition is that in this case the elimination does not make use of any information that is not already given by the mere fact that the type of argument is inhabited. This special case is known as *singleton elimination*.

.. _mutual_and_nested_inductive_definitions:

Mutual and Nested Inductive Definitions
=======================================

Lean supports two generalizations of the inductive families described above, namely, *mutual* and *nested* inductive definitions. These are *not* implemented natively in the kernel. Rather, the definitions are compiled down to the primitive inductive types and families.

The first generalization allows for multiple inductive types to be defined simultaneously.

```
mutual

inductive Foo (a : α) : Π (c : γ₁), Sort u
| constructor₁₁ : Π (b : β₁₁), Foo a t₁₁
| constructor₁₂ : Π (b : β₁₂), Foo a t₁₂
...
| constructor₁ₙ : Π (b : β₁ₙ), Foo a t₁ₙ

inductive Bar (a : α) : Π (c : γ₂), Sort u
| constructor₂₁ : Π (b : β₂₁), Bar a t₂₁
| constructor₂₂ : Π (b : β₂₂), Bar a t₂₂
...
| constructor₂ₘ : Π (b : β₂ₘ), Bar a t₂ₘ

end
```

Here the syntax is shown for defining two inductive families, ``Foo`` and ``Bar``, but any number is allowed. The restrictions are almost the same as for ordinary inductive families. For example, each ``(b : βᵢⱼ)`` is a telescope relative to the context ``(a : α)``. The difference is that the constructors can now have recursive arguments whose return types are any of the inductive families currently being defined, in this case ``Foo`` and ``Bar``. Note that all of the inductive definitions share the same parameters ``(a : α)``, though they may have different indices.

A mutual inductive definition is compiled down to an ordinary inductive definition using an extra finite-valued index to distinguish the components. The details of the internal construction are meant to be hidden from most users. Lean defines the expected type formers ``Foo`` and ``Bar`` and constructors ``constructorᵢⱼ`` from the internal inductive definition. There is no straightforward elimination principle, however. Instead, Lean defines an appropriate ``sizeOf`` measure, meant for use with well-founded recursion, with the property that the recursive arguments to a constructor are smaller than the constructed value.

The second generalization relaxes the restriction that in the recursive definition of ``Foo``, ``Foo`` can only occur strictly positively in the type of any of its recursive arguments. Specifically, in a nested inductive definition, ``Foo`` can appear as an argument to another inductive type constructor, so long as the corresponding parameter occurs strictly positively in the constructors for *that* inductive type. This process can be iterated, so that additional type constructors can be applied to those, and so on.

A nested inductive definition is compiled down to an ordinary inductive definition using a mutual inductive definition to define copies of all the nested types simultaneously. Lean then constructs isomorphisms between the mutually defined nested types and their independently defined counterparts. Once again, the internal details are not meant to be manipulated by users. Rather, the type former and constructors are made available and work as expected, while an appropriate ``sizeOf`` measure is generated for use with well-founded recursion.

```lean
universe u
-- BEGIN
mutual
inductive Even : Nat → Prop
| even_zero : Even 0
| even_succ : ∀ n, Odd n → Even (n + 1)
inductive Odd : Nat → Prop
| odd_succ : ∀ n, Even n → Odd (n + 1)
end

inductive Tree (α : Type u)
| mk : α → List (Tree α) → Tree α

inductive DoubleTree (α : Type u)
| mk : α → List (DoubleTree α) × List (DoubleTree α) → DoubleTree α
-- END
```

.. _the_equation_compiler:

The Equation Compiler
=====================

The equation compiler takes an equational description of a function or proof and tries to define an object meeting that specification. It expects input with the following syntax:

```
def foo (a : α) : Π (b : β), γ
| [patterns₁] => t₁
...
| [patternsₙ] => tₙ
```

Here ``(a : α)`` is a telescope, ``(b : β)`` is a telescope in the context ``(a : α)``, and ``γ`` is an expression in the context ``(a : α) (b : β)`` denoting a ``Type`` or a ``Prop``.

Each ``patternsᵢ`` is a sequence of patterns of the same length as ``(b : β)``. A pattern is either:

- a variable, denoting an arbitrary value of the relevant type,
- an underscore, denoting a *wildcard* or *anonymous variable*,
- an inaccessible term (see below), or
- a constructor for the inductive type of the corresponding argument, applied to a sequence of patterns.

In the last case, the pattern must be enclosed in parentheses.

Each term ``tᵢ`` is an expression in the context ``(a : α)`` together with the variables introduced on the left-hand side of the token ``=>``. The term ``tᵢ`` can also include recursive calls to ``foo``, as described below. The equation compiler does case splitting on the variables ``(b : β)`` as necessary to match the patterns, and defines ``foo`` so that it has the value ``tᵢ`` in each of the cases. In ideal circumstances (see below), the equations hold definitionally. Whether they hold definitionally or only propositionally, the equation compiler proves the relevant equations and assigns them internal names. They are accessible by the ``rewrite`` and ``simp`` tactics under the name ``foo`` (see [Rewrite](tactics.md#rewrite) and _[TODO: where is simplifier tactic documented?]_. If some of the patterns overlap, the equation compiler interprets the definition so that the first matching pattern applies in each case. Thus, if the last pattern is a variable, it covers all the remaining cases. If the patterns that are presented do not cover all possible cases, the equation compiler raises an error.

When identifiers are marked with the ``[match_pattern]`` attribute, the equation compiler unfolds them in the hopes of exposing a constructor. For example, this makes it possible to write ``n+1`` and ``0`` instead of ``Nat.succ n`` and ``Nat.zero`` in patterns.

For a nonrecursive definition involving case splits, the defining equations will hold definitionally. With inductive types like ``Char``, ``String``, and ``Fin n``, a case split would produce definitions with an inordinate number of cases. To avoid this, the equation compiler uses ``if ... then ... else`` instead of ``casesOn`` when defining the function. In this case, the defining equations hold definitionally as well.

```lean
open Nat

def sub2 : Nat → Nat
| zero          => 0
| succ zero     => 0
| succ (succ a) => a

def bar : Nat → List Nat → Bool → Nat
| 0,   _,      false => 0
| 0,   b :: _, _     => b
| 0,   [],     true  => 7
| a+1, [],     false => a
| a+1, [],     true  => a + 1
| a+1, b :: _, _     => a + b

def baz : Char → Nat
| 'A' => 1
| 'B' => 2
| _   => 3
```

The case where patterns are matched against an argument whose type is an inductive family is known as *dependent pattern matching*. This is more complicated, because the type of the function being defined can impose constraints on the patterns that are matched. In this case, the equation compiler will detect inconsistent cases and rule them out.

```lean
universe u

inductive Vector (α : Type u) : Nat → Type u
  | nil  : Vector α 0
  | cons : α → Vector α n → Vector α (n+1)

namespace Vector

def head : Vector α (n+1) → α
  | cons h t => h

def tail : Vector α (n+1) → Vector α n
  | cons h t => t

def map (f : α → β → γ) : Vector α n → Vector β n → Vector γ n
  | nil, nil => nil
  | cons a va, cons b vb => cons (f a b) (map f va vb)

end Vector
```

.. _recursive_functions:

Recursive functions
===================

Lean must ensure that a recursive function terminates, for which there are two strategies: _structural recursion_, in which all recursive calls are made on smaller parts of the input data, and _well-founded recursion_, in which recursive calls are justified by showing that arguments to recursive calls are smaller according to some other measure.

Structural recursion
--------------------

If the definition of a function contains recursive calls, Lean first tries to interpret the definition as a structural recursion. In order for that to succeed, the recursive arguments must be subterms of the corresponding arguments on the left-hand side.

The function is then defined using a *course of values* recursion, using automatically generated functions ``below`` and ``brec`` in the namespace corresponding to the inductive type of the recursive argument. In this case the defining equations hold definitionally, possibly with additional case splits.

```lean
namespace Hide

-- BEGIN
def fib : Nat → Nat
| 0     => 1
| 1     => 1
| (n+2) => fib (n+1) + fib n

def append {α : Type} : List α → List α → List α
| [],   l => l
| h::t, l => h :: append t l

example : append [(1 : Nat), 2, 3] [4, 5] = [1, 2, 3, 4, 5] => rfl
-- END

end Hide
```

Well-founded recursion
---------------------

If structural recursion fails, the equation compiler falls back on well-founded recursion. It tries to infer an instance of ``SizeOf`` for the type of each argument, and then tries to find a permutation of the arguments such that each recursive call is decreasing under the lexicographic order with respect to ``sizeOf`` measures.  Lean uses information in the local context, so you can often provide the relevant proof manually using ``have`` in the body of the definition.

In the case of well-founded recursion, the equation used to declare the function holds only propositionally, but not definitionally, and can be accessed using ``unfold``, ``simp`` and ``rewrite`` with the function name (for example ``unfold foo`` or ``simp [foo]``, where ``foo`` is the function defined with well-founded recursion).

```lean
namespace Hide
open Nat

-- BEGIN
def div : Nat → Nat → Nat
| x, y =>
  if h : 0 < y ∧ y ≤ x then
    have : x - y < x :=
      sub_lt (Nat.lt_of_lt_of_le h.left h.right) h.left
    div (x - y) y + 1
  else
    0

example (x y : Nat) :
  div x y = if 0 < y ∧ y ≤ x then div (x - y) y + 1 else 0 :=
by rw [div]; rfl
-- END

end Hide
```

If Lean cannot find a permutation of the arguments for which all recursive calls are decreasing, it will print a table that contains, for every recursive call, which arguments Lean could prove to be decreasing. For example, a function with three recursive calls and four parameters might cause the following message to be printed

```
example.lean:37:0-43:31: error: Could not find a decreasing measure.
The arguments relate at each recursive call as follows:
(<, ≤, =: relation proved, ? all proofs failed, _: no proof attempted)
           x1 x2 x3 x4
1) 39:6-27  =  =  _  =
2) 40:6-25  =  ?  _  <
3) 41:6-25  <  _  _  _
Please use `termination_by` to specify a decreasing measure.
```

This table should be read as follows:

 * In the first recursive call, in line 39, arguments 1, 2 and 4 are equal to the function's parameters.
 * The second recursive call, in line 40, has an equal first argument, a smaller fourth argument, and nothing could be inferred for the second argument.
 * The third recursive call, in line 41, has a decreasing first argument.
 * No other proofs were attempted, either because the parameter has a type without a non-trivial ``WellFounded`` instance (parameter 3), or because it is already clear that no decreasing measure can be found.


Lean will print the termination measure it found if ``set_option showInferredTerminationBy true`` is set.

If Lean does not find the termination measure, or if you want to be explicit, you can append a `termination_by` clause to the function definition, after the function's body, but before the `where` clause if present. It is of the form
```
termination_by e
```
where ``e`` is an expression that depends on the parameters of the function and should be decreasing at each recursive call. The type of `e` should be an instance of the class ``WellFoundedRelation``, which determines how to compare two values of that type.

If ``f`` has parameters “after the ``:``” (for example when defining functions via patterns using `|`), then these can be brought into scope using the syntax
```
termination_by a₁ … aₙ => e
```

By default, Lean uses the tactic ``decreasing_tactic`` when proving that an argument is decreasing; see its documentation for how to globally extend it. You can also choose to use a different tactic for a given function definition with the clause
```
decreasing_by <tac>
```
which should come after ``termination_by`, if present.


Note that recursive definitions can in general require nested recursions, that is, recursion on different arguments of ``foo`` in the template above. The equation compiler handles this by abstracting later arguments, and recursively defining higher-order functions to meet the specification.

Mutual recursion
----------------

The equation compiler also allows mutual recursive definitions, with a syntax similar to that of [Mutual and Nested Inductive Definitions](#mutual-and-nested-inductive-definitions). Mutual definitions are always compiled using well-founded recursion, and so once again the defining equations hold only propositionally.

```lean
mutual
def even : Nat → Bool
| 0   => true
| a+1 => odd a
def odd : Nat → Bool
| 0   => false
| a+1 => even a
end

example (a : Nat) : even (a + 1) = odd a :=
by simp [even]

example (a : Nat) : odd (a + 1) = even a :=
by simp [odd]
```

Well-founded recursion is especially useful with [Mutual and Nested Inductive Definitions](#mutual-and-nested-inductive-definitions), since it provides the canonical way of defining functions on these types.

```lean
mutual
inductive Even : Nat → Prop
| even_zero : Even 0
| even_succ : ∀ n, Odd n → Even (n + 1)
inductive Odd : Nat → Prop
| odd_succ : ∀ n, Even n → Odd (n + 1)
end

open Even Odd

theorem not_odd_zero : ¬ Odd 0 := fun x => nomatch x

mutual
theorem even_of_odd_succ : ∀ n, Odd (n + 1) → Even n
| _, odd_succ n h => h
theorem odd_of_even_succ : ∀ n, Even (n + 1) → Odd n
| _, even_succ n h => h
end

inductive Term
| const : String → Term
| app   : String → List Term → Term

open Term

mutual
def num_consts : Term → Nat
| .const n  => 1
| .app n ts => num_consts_lst ts
def num_consts_lst : List Term → Nat
| []    => 0
| t::ts => num_consts t + num_consts_lst ts
end
```

In a set of mutually recursive function, either all or no functions must have an explicit termination measure (``termination_by``). A change of the default termination tactic (``decreasing_by``) only affects the proofs about the recursive calls of that function, not the other functions in the group.

```
mutual
theorem even_of_odd_succ : ∀ n, Odd (n + 1) → Even n
| _, odd_succ n h => h
termination_by n h => h
decreasing_by decreasing_tactic

theorem odd_of_even_succ : ∀ n, Even (n + 1) → Odd n
| _, even_succ n h => h
termination_by n h => h
end
```

Another way to express mutual recursion is using local function definitions in ``where`` or ``let rec`` clauses: these can be mutually recursive with each other and their containing function:

```
theorem even_of_odd_succ : ∀ n, Odd (n + 1) → Even n
  | _, odd_succ n h => h
termination_by n h => h
  where
    theorem odd_of_even_succ : ∀ n, Even (n + 1) → Odd n
      | _, even_succ n h => h
    termination_by n h => h
```

.. _match_expressions:

Match Expressions
=================

Lean supports a ``match ... with ...`` construct similar to ones found in most functional programming languages. The syntax is as follows:

```
match t₁, ..., tₙ with
| p₁₁, ..., p₁ₙ => s₁
...
| pₘ₁, ..., pₘₙ => sₘ
```

Here ``t₁, ..., tₙ`` are any terms in the context in which the expression appears, the expressions ``pᵢⱼ`` are patterns, and the terms ``sᵢ`` are expressions in the local context together with variables introduced by the patterns on the left-hand side. Each ``sᵢ`` should have the expected type of the entire ``match`` expression.

Any ``match`` expression is interpreted using the equation compiler, which generalizes ``t₁, ..., tₙ``, defines an internal function meeting the specification, and then applies it to ``t₁, ..., tₙ``. In contrast to the definitions in [The Equation Compiler](declarations.md#the-equation-compiler), the terms ``tᵢ`` are arbitrary terms rather than just variables, and the expression can occur anywhere within a Lean expression, not just at the top level of a definition. Note that the syntax here is somewhat different: both the terms ``tᵢ`` and the patterns ``pᵢⱼ`` are separated by commas.

```lean
def foo (n : Nat) (b c : Bool) :=
5 + match n - 5, b && c with
    | 0,   true  => 0
    | m+1, true  => m + 7
    | 0,   false => 5
    | m+1, false => m + 3
```

When a ``match`` has only one line, Lean provides alternative syntax with a destructuring ``let``, as well as a destructuring lambda abstraction. Thus the following definitions all have the same net effect.

```lean
def bar₁ : Nat × Nat → Nat
| (m, n) => m + n

def bar₂ (p : Nat × Nat) : Nat :=
match p with | (m, n) => m + n

def bar₃ : Nat × Nat → Nat :=
fun ⟨m, n⟩ => m + n

def bar₄ (p : Nat × Nat) : Nat :=
let ⟨m, n⟩ := p; m + n
```

Information about the term being matched can be preserved in each branch using the syntax `match h : t with`. For example, a user may want to match a term `ns ++ ms : List Nat`, while tracking the hypothesis `ns ++ ms = []` or `ns ++ ms= h :: t` in the respective match arm:

```lean
def foo (ns ms : List Nat) (h1 : ns ++ ms ≠ []) (k : Nat -> Char) : Char :=
  match h2 : ns ++ ms with
  -- in this arm, we have the hypothesis `h2 : ns ++ ms = []`
  | [] => absurd h2 h1
  -- in this arm, we have the hypothesis `h2 : ns ++ ms = h :: t`
  | h :: t => k h

-- '7'
#eval foo [7, 8, 9] [] (by decide) Nat.digitChar
```

.. _structures_and_records:

Structures and Records
======================

The ``structure`` command in Lean is used to define an inductive data type with a single constructor and to define its projections at the same time. The syntax is as follows:

```
structure Foo (a : α) : Sort u extends Bar, Baz :=
constructor :: (field₁ : β₁) ... (fieldₙ : βₙ)
```

Here ``(a : α)`` is a telescope, that is, the parameters to the inductive definition. The name ``constructor`` followed by the double colon is optional; if it is not present, the name ``mk`` is used by default. The keyword ``extends`` followed by a list of previously defined structures is also optional; if it is present, an instance of each of these structures is included among the fields to ``Foo``, and the types ``βᵢ`` can refer to their fields as well. The output type, ``Sort u``, can be omitted, in which case Lean infers to smallest non-``Prop`` sort possible (unless all the fields are ``Prop``, in which case it infers ``Prop``).
Finally, ``(field₁ : β₁) ... (fieldₙ : βₙ)`` is a telescope relative to ``(a : α)`` and the fields in ``bar`` and ``baz``.

The declaration above is syntactic sugar for an inductive type declaration, and so results in the addition of the following constants to the environment:

- the type former : ``Foo : Π (a : α), Sort u``
- the single constructor :

```
Foo.constructor : Π (a : α) (toBar : Bar) (toBaz : Baz)
  (field₁ : β₁) ... (fieldₙ : βₙ), Foo a
```

- the eliminator ``Foo.rec`` for the inductive type with that constructor

In addition, Lean defines

- the projections : ``fieldᵢ : Π (a : α) (c : Foo) : βᵢ`` for each ``i``

where any other fields mentioned in ``βᵢ`` are replaced by the relevant projections from ``c``.

Given ``c : Foo``, Lean offers the following convenient syntax for the projection ``Foo.fieldᵢ c``:

- *anonymous projections* : ``c.fieldᵢ``
- *numbered projections* : ``c.i``

These can be used in any situation where Lean can infer that the type of ``c`` is of the form ``Foo a``. The convention for anonymous projections is extended to any function ``f`` defined in the namespace ``Foo``, as described in [Namespaces](namespaces.md).

Similarly, Lean offers the following convenient syntax for constructing elements of ``Foo``. They are equivalent to ``Foo.constructor b₁ b₂ f₁ f₁ ... fₙ``, where ``b₁ : Bar``, ``b₂ : Baz``, and each ``fᵢ : βᵢ`` :

- *anonymous constructor*: ``⟨ b₁, b₂, f₁, ..., fₙ ⟩``
- *record notation*:

```
{ toBar := b₁, toBaz := b₂, field₁ := f₁, ...,
    fieldₙ := fₙ :  Foo a }
```

The anonymous constructor can be used in any context where Lean can infer that the expression should have a type of the form ``Foo a``. The unicode brackets are entered as ``\<`` and ``\>`` respectively.

When using record notation, you can omit the annotation ``: Foo a`` when Lean can infer that the expression should have a type of the form ``Foo a``. You can replace either ``toBar`` or ``toBaz`` by assignments to *their* fields as well, essentially acting as though the fields of ``Bar`` and ``Baz`` are simply imported into ``Foo``. Finally, record notation also supports

- *record updates*: ``{ t with ... fieldᵢ := fᵢ ...}``

Here ``t`` is a term of type ``Foo a`` for some ``a``. The notation instructs Lean to take values from ``t`` for any field assignment that is omitted from the list.

Lean also allows you to specify a default value for any field in a structure by writing ``(fieldᵢ : βᵢ := t)``. Here ``t`` specifies the value to use when the field ``fieldᵢ`` is left unspecified in an instance of record notation.

```lean
universe u v

structure Vec (α : Type u) (n : Nat) :=
(l : List α) (h : l.length = n)

structure Foo (α : Type u) (β : Nat → Type v) : Type (max u v) :=
(a : α) (n : Nat) (b : β n)

structure Bar :=
(c : Nat := 8) (d : Nat)

structure Baz extends Foo Nat (Vec Nat), Bar :=
(v : Vec Nat n)

#check Foo
#check @Foo.mk
#check @Foo.rec

#check Foo.a
#check Foo.n
#check Foo.b

#check Baz
#check @Baz.mk
#check @Baz.rec

#check Baz.toFoo
#check Baz.toBar
#check Baz.v

def bzz := Vec.mk [1, 2, 3] rfl

#check Vec.l bzz
#check Vec.h bzz
#check bzz.l
#check bzz.h
#check bzz.1
#check bzz.2

example : Vec Nat 3 := Vec.mk [1, 2, 3] rfl
example : Vec Nat 3 := ⟨[1, 2, 3], rfl⟩
example : Vec Nat 3 := { l := [1, 2, 3], h := rfl : Vec Nat 3 }
example : Vec Nat 3 := { l := [1, 2, 3], h := rfl }

example : Foo Nat (Vec Nat) := ⟨1, 3, bzz⟩

example : Baz := ⟨⟨1, 3, bzz⟩, ⟨5, 7⟩, bzz⟩
example : Baz := { a := 1, n := 3, b := bzz, c := 5, d := 7, v := bzz}
def fzz : Foo Nat (Vec Nat) := {a := 1, n := 3, b := bzz}

example : Foo Nat (Vec Nat) := { fzz with a := 7 }
example : Baz := { fzz with c := 5, d := 7, v := bzz }

example : Bar := { c := 8, d := 9 }
example : Bar := { d := 9 }  -- uses the default value for c
```

.. _type_classes:

Type Classes
============

(Classes and instances. Anonymous instances. Local instances.)


.. [Dybjer] Dybjer, Peter, *Inductive Families*. Formal Aspects of Computing 6, 1994, pages 440-465.

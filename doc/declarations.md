# Declarations

-- TODO (fix)

Declaration Names
=================

A declaration name is a :ref:`hierarchical identifier <identifiers>` that is interpreted relative to the current namespace as well as (during lookup) to the set of open namespaces.

.. code-block:: lean

   namespace a
     constant b.c : Nat
     #print b.c -- constant a.b.c : Nat
   end a

   #print a.b.c -- constant a.b.c : Nat
   open a
   #print b.c -- constant a.b.c : Nat

Declaration names starting with an underscore are reserved for internal use. Names starting with the special atomic name ``_root_`` are interpreted as absolute names.

.. code-block:: lean

   constant a : Nat
   namespace a
     constant a : Int
     #print _root_.a -- constant a : Nat
     #print a.a      -- constant a.a : Int
   end a

Contexts and Telescopes
=======================

When processing user input, Lean first parses text to a raw expression format. It then uses background information and type constants to disambiguate overloaded symbols and infer implicit arguments, resulting in a fully-formed expression. This process is known as *elaboration*.

As hinted in :numref:`expression_syntax`, expressions are parsed and
elaborated with respect to an *environment* and a *local
context*. Roughly speaking, an environment represents the state of
Lean at the point where an expression is parsed, including previously
declared axioms, constants, definitions, and theorems. In a given
environment, a *local context* consists of a sequence ``(a₁ : α₁)
(a₂ : α₂) ... (aₙ : αₙ)`` where each ``aᵢ`` is a name denoting a local
constant and each ``αᵢ`` is an expression of type ``Sort u`` for some
``u`` which can involve elements of the environment and the local
constants ``aⱼ`` for ``j < i``.

Intuitively, a local context is a list of variables that are held constant while an expression is being elaborated. Consider the following

```lean
def f (a b : Nat) : Nat → Nat := fun c => a + (b + c)
```

Here the expression ``fun c => a + (b + c)`` is elaborated in the context ``(a : Nat) (b : Nat)`` and the expression ``a + (b + c)`` is elaborated in the context ``(a : Nat) (b : Nat) (c : Nat)``. If you replace the expression ``a + (b + c)`` with an underscore, the error message from Lean will include the current *goal*:

.. code-block:: text

   a b c : Nat
   ⊢ Nat

Here ``a b c : Nat`` indicates the local context, and the second ``Nat`` indicates the expected type of the result.

A *context* is sometimes called a *telescope*, but the latter is used more generally to include a sequence of declarations occuring relative to a given context. For example, relative to the context ``(a₁ : α₁) (a₂ : α₂) ... (aₙ : αₙ)``, the types ``βᵢ`` in a telescope ``(b₁ : β₁) (b₂ : β₂) ... (bₙ : βₙ)`` can refer to ``a₁, ..., aₙ``. Thus a context can be viewed as a telescope relative to the empty context.

Telescopes are often used to describe a list of arguments, or parameters, to a declaration. In such cases, it is often notationally convenient to let ``(a : α)`` stand for a telescope rather than just a single argument. In general, the annotations described in :ref:`implicit_arguments` can be used to mark arguments as implicit.

.. _basic_declarations:

Basic Declarations
==================

Lean provides ways of adding new objects to the environment. The following provide straightforward ways of declaring new objects:

* ``axiom c : α`` :  declare a constant named ``c`` of type ``α``, it is postulating that `α` is not an empty type.
* ``def c : α := v`` : defines ``c`` to denote ``v``, which should have type ``α``.
* ``theorem c : p := v`` : similar to ``def``, but intended to be used when ``p`` is a proposition.
* ``constant c : α (:= v)?`` : declares a opaque constant named ``c`` of type ``α``, the optional value `v` is must have type `α`
  and can be viewed as a certificate that ``α`` is not an empty type. If the value is not provided, Lean tries to find one
  using a proceture based on type class resolution. The value `v` is hidden from the type checker. You can assume that
  Lean "forgets" `v` after type checking this kind of declaration.

It is sometimes useful to be able to simulate a definition or theorem without naming it or adding it to the environment.

* ``example : α := t`` : elaborates ``t`` and checks that it has sort ``α`` (often a proposition), without adding it to the environment.

In ``def``, the type (``α`` or ``p``, respectively) can be omitted when it can be inferred by Lean. Constants declared with ``theorem`` are marked as ``irreducible``.

Any of ``def``, ``theorem``, ``axiom``, or ``example`` can take a list of arguments (that is, a context) before the colon. If ``(a : α)`` is a context, the definition ``def foo (a : α) : β := t``
is interpreted as ``def foo : (a : α) → β := fun a : α => t``. Similarly, a theorem ``theorem foo (a : α) : p := t`` is interpreted as ``theorem foo : ∀ a : α, p := fun a : α => t``.

```lean
constant c : Nat
constant d : Nat
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

.. code-block :: text

   F (constructorᵢ a b) = fᵢ b ... (fun d : δᵢⱼ => F (bⱼ d)) ...

where the ellipses include one entry for each recursive argument.

Below are some common examples of inductive types, many of which are defined in the core library.

.. code-block:: lean

  namespace hide
  universes u v

  -- BEGIN
  inductive empty : Type

  inductive unit : Type
  | star : unit

  inductive bool : Type
  | ff : bool
  | tt : bool

  inductive prod (α : Type u) (β : Type v) : Type (max u v)
  | mk : α → β → prod

  inductive sum (α : Type u) (β : Type v)
  | inl : α → sum
  | inr : β → sum

  inductive sigma (α : Type u) (β : α → Type v)
  | mk : Π a : α, β a → sigma

  inductive false : Prop

  inductive true : Prop
  | trivial : true

  inductive and (p q : Prop) : Prop
  | intro : p → q → and

  inductive or (p q : Prop) : Prop
  | inl : p → or
  | inr : q → or

  inductive Exists (α : Type u) (p : α → Prop) : Prop
  | intro : ∀ x : α, p x → Exists

  inductive subtype (α : Type u) (p : α → Prop) : Type u
  | intro : ∀ x : α, p x → subtype

  inductive nat : Type
  | zero : nat
  | succ : nat → nat

  inductive list (α : Type u)
  | nil : list
  | cons : α → list → list

  -- full binary tree with nodes and leaves labeled from α
  inductive bintree (α : Type u)
  | leaf : α → bintree
  | node : bintree → α → bintree → bintree

  -- every internal node has subtrees indexed by Nat
  inductive cbt (α : Type u)
  | leaf : α → cbt
  | node : (Nat → cbt) → cbt
  -- END
  end hide

Note that in the syntax of the inductive definition ``foo``, the context ``(a : α)`` is left implicit. In other words, constructors and recursive arguments are written as though they have return type ``foo`` rather than ``foo a``.

Elements of the context ``(a : α)`` can be marked implicit as described in :numref:`implicit_arguments`. These annotations bear only on the type former, ``foo``. Lean uses a heuristic to determine which arguments to the constructors should be marked implicit, namely, an argument is marked implicit if it can be inferred from the type of a subsequent argument. If the annotation ``{}`` appears after the constructor, a argument is marked implicit if it can be inferred from the type of a subsequent argument *or the return type*. For example, it is useful to let ``nil`` denote the empty list of any type, since the type can usually be inferred in the context in which it appears. These heuristics are imperfect, and you may sometimes wish to define your own constructors in terms of the default ones. In that case, use the ``[pattern]`` :ref:`attribute <attributes>` to ensure that these will be used appropriately by the :ref:`equation compiler <the_equation_compiler>`.

There are restrictions on the universe ``u`` in the return type ``Sort u`` of the type former. There are also restrictions on the universe ``u`` in the return type ``Sort u`` of the motive of the eliminator. These will be discussed in the next section in the more general setting of inductive families.

Lean allows some additional syntactic conveniences. You can omit the return type of the type former, ``Sort u``, in which case Lean will infer the minimal possible nonzero value for ``u``. As with function definitions, you can list arguments to the constructors before the colon. In an enumerated type (that is, one where the constructors have no arguments), you can also leave out the return type of the constructors.

.. code-block:: lean

  namespace hide
  universe u

  -- BEGIN
  inductive weekday
  | sunday | monday | tuesday | wednesday
  | thursday | friday | saturday

  inductive nat
  | zero
  | succ (n : nat) : nat

  inductive list (α : Type u)
  | nil {} : list
  | cons (a : α) (l : list) : list

  @[pattern]
  def list.nil' (α : Type u) : list α := list.nil

  def length {α : Type u} : list α → Nat
  | (list.nil' .(α)) := 0
  | (list.cons a l) := 1 + length l
  -- END

  end hide

The type former, constructors, and eliminator are all part of Lean's axiomatic foundation, which is to say, they are part of the trusted kernel. In addition to these axiomatically declared constants, Lean automatically defines some additional objects in terms of these, and adds them to the environment. These include the following:

- ``foo.rec_on`` : a variant of the eliminator, in which the major premise comes first
- ``foo.cases_on`` : a restricted version of the eliminator which omits any recursive calls
- ``foo.no_confusion_type``, ``foo.no_confusion`` : functions which witness the fact that the inductive type is freely generated, i.e. that the constructors are injective and that distinct constructors produce distinct objects
- ``foo.below``, ``foo.ibelow`` : functions used by the equation compiler to implement structural recursion
- ``foo.sizeof`` : a measure which can be used for well-founded recursion

Note that it is common to put definitions and theorems related to a datatype ``foo`` in a namespace of the same name. This makes it possible to use projection notation described in :numref:`structures_and_records` and :numref:`namespaces`.

.. code-block:: lean

  namespace hide
  universe u

  -- BEGIN
  inductive nat
  | zero
  | succ (n : nat) : nat

  #check nat
  #check nat.rec
  #check nat.zero
  #check nat.succ

  #check nat.rec_on
  #check nat.cases_on
  #check nat.no_confusion_type
  #check @nat.no_confusion
  #check nat.brec_on
  #check nat.below
  #check nat.ibelow
  #check nat.sizeof

  -- END

  end hide

.. _inductive_families:

Inductive Families
==================

In fact, Lean implements a slight generalization of the inductive types described in the previous section, namely, inductive *families*. The declaration of an inductive family in Lean has the following form:

.. code-block:: text

   inductive foo (a : α) : Π (c : γ), Sort u
   | constructor₁ : Π (b : β₁), foo t₁
   | constructor₂ : Π (b : β₂), foo t₂
   ...
   | constructorₙ : Π (b : βₙ), foo tₙ

Here ``(a : α)`` is a context, ``(c : γ)`` is a telescope in context ``(a : α)``, each ``(b : βᵢ)`` is a telescope in the context ``(a : α)`` together with ``(foo : Π (c : γ), Sort u)`` subject to the constraints below, and each ``tᵢ`` is a tuple of terms in the context ``(a : α) (b : βᵢ)`` having the types ``γ``. Instead of defining a single inductive type ``foo a``, we are now defining a family of types ``foo a c`` indexed by elements ``c : γ``.  Each constructor, ``constructorᵢ``, places its result in the type ``foo a tᵢ``, the member of the family with index ``tᵢ``.

The modifications to the scheme in the previous section are straightforward. Suppose the telescope ``(b : βᵢ)`` is ``(b₁ : βᵢ₁) ... (bᵤ : βᵢᵤ)``.

- As before, an argument ``(bⱼ : βᵢⱼ)`` is *nonrecursive* if ``βᵢⱼ`` does not refer to ``foo,`` the inductive type being defined. In that case, ``βᵢⱼ`` can be any type, so long as it does not refer to any nonrecursive arguments.

- An argument ``(bⱼ : βᵢⱼ)`` is *recursive* if ``βᵢⱼ`` is of the form ``Π (d : δ), foo s`` where ``(d : δ)`` is a telescope which does not refer to ``foo`` or any nonrecursive arguments and ``s`` is a tuple of terms in context ``(a : α)`` and the previous nonrecursive ``bⱼ``'s with types ``γ``.

The declaration of the type ``foo`` as above results in the addition of the following constants to the environment:

- the *type former* ``foo : Π (a : α) (c : γ), Sort u``
- for each ``i``, the *constructor* ``foo.constructorᵢ : Π (a : α) (b : βᵢ), foo a tᵢ``
- the *eliminator* ``foo.rec``, which takes arguments

  + ``(a : α)`` (the parameters)
  + ``{C : Π (c : γ), foo a c → Type u}`` (the motive of the elimination)
  + for each ``i``, the minor premise corresponding to ``constructorᵢ``
  + ``(x : foo a)`` (the major premise)

  and returns an element of ``C x``. Here, The ith minor premise is a function which takes

  +  ``(b : βᵢ)`` (the arguments to the constructor)
  + an argument of type ``Π (d : δ), C s (bⱼ d)`` corresponding to each recursive argument ``(bⱼ : βᵢⱼ)``, where ``βᵢⱼ``  is of the form ``Π (d : δ), foo s``

  and returns an element of ``C tᵢ (constructorᵢ a b)``.

Suppose we set ``F := foo.rec a C f₁ ... fₙ``. Then for each constructor, we have the definitional reduction, as before:

.. code-block :: text

   F (constructorᵢ a b) = fᵢ b ... (fun d : δᵢⱼ => F (bⱼ d)) ...

where the ellipses include one entry for each recursive argument.

The following are examples of inductive families.

.. code-block:: lean

  namespace hide
  universe u

  -- BEGIN
  inductive vector (α : Type u) : Nat → Type u
  | nil  : vector 0
  | succ : Π n, vector n → vector (n + 1)

  -- 'is_prod s n' means n is a product of elements of s
  inductive is_prod (s : set Nat) : Nat → Prop
  | base : ∀ n ∈ s, is_prod n
  | step : ∀ m n, is_prod m → is_prod n → is_prod (m * n)

  inductive eq {α : Sort u} (a : α) : α → Prop
  | refl : eq a
  -- END

  end hide

We can now describe the constraints on the return type of the type former, ``Sort u``. We can always take ``u`` to be ``0``, in which case we are defining an inductive family of propositions. If ``u`` is nonzero, however, it must satisfy the following constraint: for each type ``βᵢⱼ : Sort v`` occurring in the constructors, we must have ``u ≥ v``. In the set-theoretic interpretation, this ensures that the universe in which the resulting type resides is large enough to contain the inductively generated family, given the number of distinctly-labeled constructors. The restriction does not hold for inductively defined propositions, since these contain no data.

Putting an inductive family in ``Prop``, however, does impose a restriction on the eliminator. Generally speaking, for an inductive family in ``Prop``, the motive in the eliminator is required to be in ``Prop``. But there is an exception to this rule: you are allowed to eliminate from an inductively defined ``Prop`` to an arbitrary ``Sort`` when there is only one constructor, and each argument to that constructor is either in ``Prop`` or an index. The intuition is that in this case the elimination does not make use of any information that is not already given by the mere fact that the type of argument is inhabited. This special case is known as *singleton elimination*.

.. _mutual_and_nested_inductive_definitions:

Mutual and Nested Inductive Definitions
=======================================

Lean supports two generalizations of the inductive families described above, namely, *mutual* and *nested* inductive definitions. These are *not* implemented natively in the kernel. Rather, the definitions are compiled down to the primitive inductive types and families.

The first generalization allows for multiple inductive types to be defined simultaneously.

.. code-block:: text

   mutual inductive foo, bar (a : α)
   with foo : Π (c : γ), Sort u
   | constructor₁₁ : Π (b : β₁₁), foo t₁₁
   | constructor₁₂ : Π (b : β₁₂), foo t₁₂
   ...
   | constructor₁ₙ : Π (b : β₁ₙ), foo t₁ₙ
   with bar :
   | constructor₂₁ : Π (b : β₂₁), bar t₂₁
   | constructor₂₂ : Π (b : β₂₂), bar t₂₂
   ...
   | constructor₂ₘ : Π (b : β₂ₘ), bar t₂ₘ

Here the syntax is shown for defining two inductive families, ``foo`` and ``bar``, but any number is allowed. The restrictions are almost the same as for ordinary inductive families. For example, each ``(b : βᵢⱼ)`` is a telescope relative to the context ``(a : α)``. The difference is that the constructors can now have recursive arguments whose return types are any of the inductive families currently being defined, in this case ``foo`` and ``bar``. Note that all of the inductive definitions share the same parameters ``(a : α)``, though they may have different indices.

A mutual inductive definition is compiled down to an ordinary inductive definition using an extra finite-valued index to distinguish the components. The details of the internal construction are meant to be hidden from most users. Lean defines the expected type formers ``foo`` and ``bar`` and constructors ``constructorᵢⱼ`` from the internal inductive definition. There is no straightforward elimination principle, however. Instead, Lean defines an appropriate ``sizeof`` measure, meant for use with well-founded recursion, with the property that the recursive arguments to a constructor are smaller than the constructed value.

The second generalization relaxes the restriction that in the recursive definition of ``foo``, ``foo`` can only occur strictly positively in the type of any of its recursive arguments. Specifically, in a nested inductive definition, ``foo`` can appear as an argument to another inductive type constructor, so long as the corresponding parameter occurs strictly positively in the constructors for *that* inductive type. This process can be iterated, so that additional type constructors can be applied to those, and so on.

A nested inductive definition is compiled down to an ordinary inductive definition using a mutual inductive definition to define copies of all the nested types simultaneously. Lean then constructs isomorphisms between the mutually defined nested types and their independently defined counterparts. Once again, the internal details are not meant to be manipulated by users. Rather, the type former and constructors are made available and work as expected, while an appropriate ``sizeof`` measure is generated for use with well-founded recursion.

.. code-block:: lean

    universe u
    -- BEGIN
    mutual inductive even, odd
    with even : Nat → Prop
    | even_zero : even 0
    | even_succ : ∀ n, odd n → even (n + 1)
    with odd : Nat → Prop
    | odd_succ : ∀ n, even n → odd (n + 1)

    inductive tree (α : Type u)
    | mk : α → list tree → tree

    inductive double_tree (α : Type u)
    | mk : α → list double_tree × list double_tree → double_tree
    -- END

.. _the_equation_compiler:

The Equation Compiler
=====================

The equation compiler takes an equational description of a function or proof and tries to define an object meeting that specification. It expects input with the following syntax:

.. code-block:: text

    def foo (a : α) : Π (b : β), γ
    | [patterns₁] := t₁
    ...
    | [patternsₙ] := tₙ

Here ``(a : α)`` is a telescope, ``(b : β)`` is a telescope in the context ``(a : α)``, and ``γ`` is an expression in the context ``(a : α) (b : β)`` denoting a ``Type`` or a ``Prop``.

Each ``patternsᵢ`` is a sequence of patterns of the same length as ``(b : β)``. A pattern is either:

- a variable, denoting an arbitrary value of the relevant type,
- an underscore, denoting a *wildcard* or *anonymous variable*,
- an inaccessible term (see below), or
- a constructor for the inductive type of the corresponding argument, applied to a sequence of patterns.

In the last case, the pattern must be enclosed in parentheses.

Each term ``tᵢ`` is an expression in the context ``(a : α)`` together with the variables introduced on the left-hand side of the token ``:=``. The term ``tᵢ`` can also include recursive calls to ``foo``, as described below. The equation compiler does case splitting on the variables ``(b : β)`` as necessary to match the patterns, and defines ``foo`` so that it has the value ``tᵢ`` in each of the cases. In ideal circumstances (see below), the equations hold definitionally. Whether they hold definitionally or only propositionally, the equation compiler proves the relevant equations and assigns them internal names. They are accessible by the ``rewrite`` and ``simp`` tactics under the name ``foo`` (see :numref:`the_rewriter` and :numref:`the_simplifier`). If some of the patterns overlap, the equation compiler interprets the definition so that the first matching pattern applies in each case. Thus, if the last pattern is a variable, it covers all the remaining cases. If the patterns that are presented do not cover all possible cases, the equation compiler raises an error.

When identifiers are marked with the ``[pattern]`` attribute, the equation compiler unfolds them in the hopes of exposing a constructor. For example, this makes it possible to write ``n+1`` and ``0`` instead of ``nat.succ n`` and ``nat.zero`` in patterns.

For a nonrecursive definition involving case splits, the defining equations will hold definitionally. With inductive types like ``char``, ``string``, and ``fin n``, a case split would produce definitions with an inordinate number of cases. To avoid this, the equation compiler uses ``if ... then ... else`` instead of ``cases_on`` when defining the function. In this case, the defining equations hold definitionally as well.

.. code-block:: lean

    open nat

    def sub2 : Nat → Nat
    | zero            := 0
    | (succ zero)     := 0
    | (succ (succ a)) := a

    def bar : Nat → list Nat → bool → Nat
    | 0     _        ff := 0
    | 0     (b :: _) _  := b
    | 0     []       tt := 7
    | (a+1) []       ff := a
    | (a+1) []       tt := a + 1
    | (a+1) (b :: _) _  := a + b

    def baz : char → Nat
    | 'A' := 1
    | 'B' := 2
    | _   := 3

If any of the terms ``tᵢ`` in the template above contain a recursive call to ``foo``, the equation compiler tries to interpret the definition as a structural recursion. In order for that to succeed, the recursive arguments must be subterms of the corresponding arguments on the left-hand side. The function is then defined using a *course of values* recursion, using automatically generated functions ``below`` and ``brec`` in the namespace corresponding to the inductive type of the recursive argument. In this case the defining equations hold definitionally, possibly with additional case splits.

.. code-block:: lean

    namespace hide

    -- BEGIN
    def fib : nat → nat
    | 0     := 1
    | 1     := 1
    | (n+2) := fib (n+1) + fib n

    def append {α : Type} : list α → list α → list α
    | []     l := l
    | (h::t) l := h :: append t l

    example : append [(1 : Nat), 2, 3] [4, 5] = [1, 2, 3, 4, 5] := rfl
    -- END

    end hide

If structural recursion fails, the equation compiler falls back on well-founded recursion. It tries to infer an instance of ``has_sizeof`` for the type of each argument, and then show that each recursive call is decreasing under the lexicographic order of the arguments with respect to ``sizeof`` measure. If it fails, the error message provides information as to the goal that Lean tried to prove. Lean uses information in the local context, so you can often provide the relevant proof manually using ``have`` in the body of the definition. In this case of well-founded recursion, the defining equations hold only propositionally, and can be accessed using ``simp`` and ``rewrite`` with the name ``foo``.

.. code-block:: lean

    namespace hide
    open nat

    -- BEGIN
    def div : Nat → Nat → Nat
    | x y :=
      if h : 0 < y ∧ y ≤ x then
        have x - y < x,
          from sub_lt (lt_of_lt_of_le h.left h.right) h.left,
        div (x - y) y + 1
      else
        0

    example (x y : Nat) :
      div x y = if 0 < y ∧ y ≤ x then div (x - y) y + 1 else 0 :=
    by rw [div]
    -- END

    end hide

Note that recursive definitions can in general require nested recursions, that is, recursion on different arguments of ``foo`` in the template above. The equation compiler handles this by abstracting later arguments, and recursively defining higher-order functions to meet the specification.

The equation compiler also allows mutual recursive definitions, with a syntax similar to that of :ref:`mutual inductive definitions <mutual_and_nested_inductive_definitions>`. They are compiled using well-founded recursion, and so once again the defining equations hold only propositionally.

.. code-block:: lean

    mutual def even, odd
    with even : Nat → bool
    | 0     := tt
    | (a+1) := odd a
    with odd : Nat → bool
    | 0     := ff
    | (a+1) := even a

    example (a : Nat) : even (a + 1) = odd a :=
    by simp [even]

    example (a : Nat) : odd (a + 1) = even a :=
    by simp [odd]

Well-founded recursion is especially useful with :ref:`mutual and nested inductive definitions <mutual_and_nested_inductive_definitions>`, since it provides the canonical way of defining functions on these types.

.. code-block:: lean

    mutual inductive even, odd
    with even : Nat → Prop
    | even_zero : even 0
    | even_succ : ∀ n, odd n → even (n + 1)
    with odd : Nat → Prop
    | odd_succ : ∀ n, even n → odd (n + 1)

    open even odd

    theorem not_odd_zero : ¬ odd 0.

    mutual theorem even_of_odd_succ, odd_of_even_succ
    with even_of_odd_succ : ∀ n, odd (n + 1) → even n
    | _ (odd_succ n h) := h
    with odd_of_even_succ : ∀ n, even (n + 1) → odd n
    | _ (even_succ n h) := h

    inductive term
    | const : string → term
    | app   : string → list term → term

    open term

    mutual def num_consts, num_consts_lst
    with num_consts : term → nat
    | (term.const n)  := 1
    | (term.app n ts) := num_consts_lst ts
    with num_consts_lst : list term → nat
    | []      := 0
    | (t::ts) := num_consts t + num_consts_lst ts

The case where patterns are matched against an argument whose type is an inductive family is known as *dependent pattern matching*. This is more complicated, because the type of the function being defined can impose constraints on the patterns that are matched. In this case, the equation compiler will detect inconsistent cases and rule them out.

.. code-block:: lean

    universe u

    inductive vector (α : Type u) : Nat → Type u
    | nil {} : vector 0
    | cons   : Π {n}, α → vector n → vector (n+1)

    namespace vector

    def head {α : Type} : Π {n}, vector α (n+1) → α
    | n (cons h t) := h

    def tail {α : Type} : Π {n}, vector α (n+1) → vector α n
    | n (cons h t) := t

    def map {α β γ : Type} (f : α → β → γ) :
      Π {n}, vector α n → vector β n → vector γ n
    | 0     nil         nil         := nil
    | (n+1) (cons a va) (cons b vb) := cons (f a b) (map va vb)

    end vector

An expression of the form ``.(t)`` in a pattern is known as an *inaccessible term*. It is not viewed as part of the pattern; rather, it is explicit information that is used by the elaborator and equation compiler when interpreting the definition. Inaccessible terms do not participate in pattern matching. They are sometimes needed for a pattern to make sense, for example, when a constructor depends on a parameter that is not a pattern-matching variable. In other cases, they can be used to inform the equation compiler that certain arguments do not require a case split, and they can be used to make a definition more readable.

.. code-block:: lean

    universe u

    inductive vector (α : Type u) : Nat → Type u
    | nil {} : vector 0
    | cons   : Π {n}, α → vector n → vector (n+1)

    namespace vector

    -- BEGIN
    variable {α : Type u}

    def add [has_add α] :
      Π {n : Nat}, vector α n → vector α n → vector α n
    | ._ nil        nil        := nil
    | ._ (cons a v) (cons b w) := cons (a + b) (add v w)

    def add' [has_add α] :
      Π {n : Nat}, vector α n → vector α n → vector α n
    | .(0)   nil                nil        := nil
    | .(n+1) (@cons .(α) n a v) (cons b w) := cons (a + b) (add' v w)
    -- END

    end vector

.. _match_expressions:

Match Expressions
=================

Lean supports a ``match ... with ...`` construct similar to ones found in most functional programming languages. The syntax is as follows:

.. code-block:: text

    match t₁, ..., tₙ with
    | p₁₁, ..., p₁ₙ := s₁
    ...
    | pₘ₁, ..., pₘₙ := sₘ

Here ``t₁, ..., tₙ`` are any terms in the context in which the expression appears, the expressions ``pᵢⱼ`` are patterns, and the terms ``sᵢ`` are expressions in the local context together with variables introduced by the patterns on the left-hand side. Each ``sᵢ`` should have the expected type of the entire ``match`` expression.

Any ``match`` expression is interpreted using the equation compiler, which generalizes ``t₁, ..., tₙ``, defines an internal function meeting the specification, and then applies it to ``t₁, ..., tₙ``. In contrast to the definitions in :numref:`the_equation_compiler`, the terms ``tᵢ`` are arbitrary terms rather than just variables, and the expression can occur anywhere within a Lean expression, not just at the top level of a definition. Note that the syntax here is somewhat different: both the terms ``tᵢ`` and the patterns ``pᵢⱼ`` are separated by commas.

.. code-block:: lean

    def foo (n : Nat) (b c : bool) :=
    5 + match n - 5, b && c with
        | 0,      tt := 0
        | m+1,    tt := m + 7
        | 0,      ff := 5
        | m+1,    ff := m + 3
        end

When a ``match`` has only one line, the vertical bar may be left out. In that case, Lean provides alternative syntax with a destructuring ``let``, as well as a destructuring lambda abstraction. Thus the following definitions all have the same net effect.

.. code-block:: lean

    def bar₁ : Nat × Nat → Nat
    | (m, n) := m + n

    def bar₂ (p : Nat × Nat) : Nat :=
    match p with (m, n) := m + n end

    def bar₃ : Nat × Nat → Nat :=
    fun ⟨m, n⟩ => m + n

    def bar₄ (p : Nat × Nat) : Nat :=
    let ⟨m, n⟩ := p in m + n

.. _structures_and_records:

Structures and Records
======================

The ``structure`` command in Lean is used to define an inductive data type with a single constructor and to define its projections at the same time. The syntax is as follows:

.. code-block:: text

    structure foo (a : α) extends bar, baz : Sort u :=
    constructor :: (field₁ : β₁) ... (fieldₙ : βₙ)

Here ``(a : α)`` is a telescope, that is, the parameters to the inductive definition. The name ``constructor`` followed by the double colon is optional; if it is not present, the name ``mk`` is used by default. The keyword ``extends`` followed by a list of previously defined structures is also optional; if it is present, an instance of each of these structures is included among the fields to ``foo,`` and the types ``βᵢ`` can refer to their fields as well. The output type, ``Sort u``, can be omitted, in which case Lean infers to smallest non-``Prop`` sort possible. Finally, ``(field₁ : β₁) ... (fieldₙ : βₙ)`` is a telescope relative to ``(a : α)`` and the fields in ``bar`` and ``baz``.

The declaration above is syntactic sugar for an inductive type declaration, and so results in the addition of the following constants to the environment:

- the type former : ``foo : Π (a : α), Sort u``
- the single constructor :

  .. code-block:: text

     foo.constructor : Π (a : α) (_to_foo : foo) (_to_bar : bar)
       (field₁ : β₁) ... (fieldₙ : βₙ), foo a

- the eliminator ``foo.rec`` for the inductive type with that constructor

In addition, Lean defines

- the projections : ``fieldᵢ : Π (a : α) (c : foo) : βᵢ`` for each ``i``

where any other fields mentioned in ``βᵢ`` are replaced by the relevant projections from ``c``.

Given ``c : foo``, Lean offers the following convenient syntax for the projection ``foo.fieldᵢ c``:

- *anonymous projections* : ``c.fieldᵢ``
- *numbered projections* : ``c.i``

These can be used in any situation where Lean can infer that the type of ``c`` is of the form ``foo a``. The convention for anonymous projections is extended to any function ``f`` defined in the namespace ``foo``, as described in :numref:`namespaces`.

Similarly, Lean offers the following convenient syntax for constructing elements of ``foo``. They are equivalent to ``foo.constructor b₁ b₂ f₁ f₁ ... fₙ``, where ``b₁ : foo``, ``b₂ : bar``, and each ``fᵢ : βᵢ`` :

- *anonymous constructor*: ``⟨ b₁, b₂, f₁, ..., fₙ ⟩``
- *record notation*:

  .. code-block:: text

     { foo . to_bar := b₁, to_baz := b₂, field₁ := f₁, ...,
         fieldₙ := fₙ }

The anonymous constructor can be used in any context where Lean can infer that the expression should have a type of the form ``foo a``. The unicode brackets are entered as ``\<`` and ``\>`` respectively. The tokens ``(|`` and ``|)`` are ascii equivalents.

When using record notation, you can omit the annotation ``foo .`` when Lean can infer that the expression should have a type of the form ``foo a``. You can replace either ``to_bar`` or ``to_baz`` by assignments to *their* fields as well, essentially acting as though the fields of ``bar`` and ``baz`` are simply imported into ``foo``. Finally, record notation also supports

- *record updates*: ``{ t with ... fieldᵢ := fᵢ ...}``

Here ``t`` is a term of type ``foo a`` for some ``a``. The notation instructs Lean to take values from ``t`` for any field assignment that is omitted from the list.

Lean also allows you to specify a default value for any field in a structure by writing ``(fieldᵢ : βᵢ := t)``. Here ``t`` specifies the value to use when the field ``fieldᵢ`` is left unspecified in an instance of record notation.

.. code-block:: lean

    universes u v

    structure vec (α : Type u) (n : Nat) :=
    (l : list α) (h : l.length = n)

    structure foo (α : Type u) (β : Nat → Type v) : Type (max u v) :=
    (a : α) (n : Nat) (b : β n)

    structure bar :=
    (c : Nat := 8) (d : Nat)

    structure baz extends foo Nat (vec Nat), bar :=
    (v : vec Nat n)

    #check foo
    #check @foo.mk
    #check @foo.rec

    #check foo.a
    #check foo.n
    #check foo.b

    #check baz
    #check @baz.mk
    #check @baz.rec

    #check baz.to_foo
    #check baz.to_bar
    #check baz.v

    def bzz := vec.mk [1, 2, 3] rfl

    #check vec.l bzz
    #check vec.h bzz
    #check bzz.l
    #check bzz.h
    #check bzz.1
    #check bzz.2

    example : vec Nat 3 := vec.mk [1, 2, 3] rfl
    example : vec Nat 3 := ⟨[1, 2, 3], rfl⟩
    example : vec Nat 3 := (| [1, 2, 3], rfl |)
    example : vec Nat 3 := { vec . l := [1, 2, 3], h := rfl }
    example : vec Nat 3 := { l := [1, 2, 3], h := rfl }

    example : foo Nat (vec Nat) := ⟨1, 3, bzz⟩

    example : baz := ⟨⟨1, 3, bzz⟩, ⟨5, 7⟩, bzz⟩
    example : baz := { a := 1, n := 3, b := bzz, c := 5, d := 7, v := bzz}
    def fzz : foo Nat (vec Nat) := {a := 1, n := 3, b := bzz}

    example : foo Nat (vec Nat) := { fzz with a := 7 }
    example : baz := { fzz with c := 5, d := 7, v := bzz }

    example : bar := { c := 8, d := 9 }
    example : bar := { d := 9 }  -- uses the default value for c

.. _type_classes:

Type Classes
============

(Classes and instances. Anonymous instances. Local instances.)


.. [Dybjer] Dybjer, Peter, *Inductive Families*. Formal Aspects of Computing 6, 1994, pages 440-465.

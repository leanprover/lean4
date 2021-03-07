## Types as objects

One way in which Lean's dependent type theory extends simple type theory is that types themselves --- entities like ``Nat`` and ``Bool`` ---
are first-class citizens, which is to say that they themselves are objects. For that to be the case, each of them also has to have a type.

```lean
#check Nat               -- Type
#check Bool              -- Type
#check Nat → Bool        -- Type
#check Nat × Bool        -- Type
#check Nat → Nat         -- ...
#check Nat × Nat → Nat
#check Nat → Nat → Nat
#check Nat → (Nat → Nat)
#check Nat → Nat → Bool
#check (Nat → Nat) → Nat
```

We see that each one of the expressions above is an object of type ``Type``. We can also declare new constants and constructors for types:

```lean
constant α : Type
constant β : Type
constant F : Type → Type
constant G : Type → Type → Type

#check α        -- Type
#check F α      -- Type
#check F Nat    -- Type
#check G α      -- Type → Type
#check G α β    -- Type
#check G α Nat  -- Type
```

Indeed, we have already seen an example of a function of type ``Type → Type → Type``, namely, the Cartesian product.

```lean
constant α : Type
constant β : Type

#check Prod α β       -- Type
#check Prod Nat Nat   -- Type
```

Here is another example: given any type ``α``, the type ``List α`` denotes the type of lists of elements of type ``α``.

```lean
constant α : Type

#check List α    -- Type
#check List Nat  -- Type
```

Given that every expression in Lean has a type, it is natural to ask: what type does ``Type`` itself have?

```lean
#check Type      -- Type 1
```

We have actually come up against one of the most subtle aspects of Lean's typing system.
Lean's underlying foundation has an infinite hierarchy of types:

```lean
#check Type     -- Type 1
#check Type 1   -- Type 2
#check Type 2   -- Type 3
#check Type 3   -- Type 4
#check Type 4   -- Type 5
```

Think of ``Type 0`` as a universe of "small" or "ordinary" types.
``Type 1`` is then a larger universe of types, which contains ``Type 0`` as an element,
and ``Type 2`` is an even larger universe of types, which contains ``Type 1`` as an element.
The list is indefinite, so that there is a ``Type n`` for every natural number ``n``.
``Type`` is an abbreviation for ``Type 0``:

```lean
#check Type
#check Type 0
```

There is also another type universe, ``Prop``, which has special properties.

```lean
#check Prop -- Type
```

We will discuss ``Prop`` later.

We want some operations, however, to be *polymorphic* over type universes. For example, ``List α`` should
make sense for any type ``α``, no matter which type universe ``α`` lives in. This explains the type annotation of the function ``List``:

```lean
#check List    -- Type u_1 → Type u_1
```

Here ``u_1`` is a variable ranging over type levels. The output of the ``#check`` command means that whenever ``α`` has type ``Type n``, ``List α`` also has type ``Type n``. The function ``Prod`` is similarly polymorphic:

```lean
#check Prod    -- Type u_1 → Type u_2 → Type (max u_1 u_2)
```

To define polymorphic constants and variables, Lean allows us to declare universe variables explicitly using the `universe` command:

```lean
universe u
constant α : Type u
#check α
```
Equivalently, we can write ``Type _`` to avoid giving the arbitrary universe a name:

```lean
constant α : Type _
#check α
```

Several Lean 3 users use the shorthand `Type*` for `Type _`. The `Type*` notation is not builtin in Lean 4, but you can easily define it using a `macro`.
```lean
macro "Type*" : term => `(Type _)

def f (α : Type*) (a : α) := a

def g (α : Type _) (a : α) := a

#check f
#check g
```

We explain later how the `macro` command works.

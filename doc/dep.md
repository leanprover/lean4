## What makes dependent type theory dependent?

The short explanation is that what makes dependent type theory dependent is that types can depend on parameters.
You have already seen a nice example of this: the type ``List α`` depends on the argument ``α``, and
this dependence is what distinguishes ``List Nat`` and ``List Bool``.
For another example, consider the type ``Vector α n``, the type of vectors of elements of ``α`` of length ``n``.
This type depends on *two* parameters: the type ``α : Type`` of the elements in the vector and the length ``n : Nat``.

Suppose we wish to write a function ``cons`` which inserts a new element at the head of a list.
What type should ``cons`` have? Such a function is *polymorphic*: we expect the ``cons`` function for ``Nat``, ``Bool``,
or an arbitrary type ``α`` to behave the same way.
So it makes sense to take the type to be the first argument to ``cons``, so that for any type, ``α``, ``cons α``
is the insertion function for lists of type ``α``. In other words, for every ``α``, ``cons α`` is the function that takes an element ``a : α``
and a list ``as : List α``, and returns a new list, so we have ``cons α a as : list α``.

It is clear that ``cons α`` should have type ``α → List α → List α``. But what type should ``cons`` have?
A first guess might be ``Type → α → list α → list α``, but, on reflection, this does not make sense:
the ``α`` in this expression does not refer to anything, whereas it should refer to the argument of type ``Type``.
In other words, *assuming* ``α : Type`` is the first argument to the function, the type of the next two elements are ``α`` and ``List α``.
These types vary depending on the first argument, ``α``.

This is an instance of a *dependent function type*, or *dependent arrow type*. Given ``α : Type`` and ``β : α → Type``,
think of ``β`` as a family of types over ``α``, that is, a type ``β a`` for each ``a : α``.
In that case, the type ``(a : α) → β a`` denotes the type of functions ``f`` with the property that,
for each ``a : α``, ``f a`` is an element of ``β a``. In other words, the type of the value returned by ``f`` depends on its input.

Notice that ``(a : α) → β`` makes sense for any expression ``β : Type``. When the value of ``β`` depends on ``a``
(as does, for example, the expression ``β a`` in the previous paragraph), ``(a : α) → β`` denotes a dependent function type.
When ``β`` doesn't depend on ``a``, ``(a : α) → β`` is no different from the type ``α → β``.
Indeed, in dependent type theory (and in Lean), ``α → β`` is just notation for ``(a : α) → β`` when ``β`` does not depend on ``a``.

Returning to the example of lists, we can use the command `#check` to inspect the type of the following `List` functions
We will explain the ``@`` symbol and the difference between the round and curly braces momentarily.

```lean
#check @List.cons    -- {α : Type u_1} → α → List α → List α
#check @List.nil     -- {α : Type u_1} → List α
#check @List.length  -- {α : Type u_1} → List α → Nat
#check @List.append  -- {α : Type u_1} → List α → List α → List α
```

Just as dependent function types ``(a : α) → β a`` generalize the notion of a function type ``α → β`` by allowing ``β`` to depend on ``α``,
dependent Cartesian product types ``(a : α) × β a`` generalize the Cartesian product ``α × β`` in the same way. Dependent products are also
called *sigma* types, and you can also write them as `Σ a : α, β a`. You can use `⟨a, b⟩` or `Sigma.mk a b` to create a dependent pair.

```lean
universe u v

def f (α : Type u) (β : α → Type v) (a : α) (b : β a) : (a : α) × β a :=
  ⟨a, b⟩

def g (α : Type u) (β : α → Type v) (a : α) (b : β a) : Σ a : α, β a :=
  Sigma.mk a b

#reduce f
#reduce g

#reduce f Type (fun α => α) Nat 10
#reduce g Type (fun α => α) Nat 10

#reduce (f Type (fun α => α) Nat 10).1 -- Nat
#reduce (g Type (fun α => α) Nat 10).1 -- Nat
#reduce (f Type (fun α => α) Nat 10).2 -- 10
#reduce (g Type (fun α => α) Nat 10).2 -- 10
```
The function `f` and `g` above denote the same function.

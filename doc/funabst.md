## Function Abstraction and Evaluation

We have seen that if we have ``m n : Nat``, then we have ``(m, n) : Nat × Nat``.
This gives us a way of creating pairs of natural numbers.
Conversely, if we have ``p : Nat × Nat``, then
we have ``p.1 : Nat`` and ``p.2 : Nat``.
This gives us a way of "using" a pair, by extracting its two components.

We already know how to "use" a function ``f : α → β``, namely,
we can apply it to an element ``a : α`` to obtain ``f a : β``.
But how do we create a function from another expression?

The companion to application is a process known as "lambda abstraction."
Suppose that giving a variable ``x : α`` we can construct an expression ``t : β``.
Then the expression ``fun (x : α) => t``, or, equivalently, ``λ (x : α) => t``, is an object of type ``α → β``.
Think of this as the function from ``α`` to ``β`` which maps any value ``x`` to the value ``t``,
which may depend on ``x``.

```lean
#check fun (x : Nat) => x + 5
#check λ (x : Nat) => x + 5
#check fun x : Nat => x + 5
#check λ x : Nat => x + 5
```

Here are some more examples:

```lean
constant f : Nat → Nat
constant h : Nat → Bool → Nat

#check fun x : Nat => fun y : Bool => h (f x) y   -- Nat → Bool → Nat
#check fun (x : Nat) (y : Bool) => h (f x) y      -- Nat → Bool → Nat
#check fun x y => h (f x) y                       -- Nat → Bool → Nat
```

Lean interprets the final three examples as the same expression; in the last expression,
Lean infers the type of ``x`` and ``y`` from the types of ``f`` and ``h``.

Some mathematically common examples of operations of functions can be described in terms of lambda abstraction:

```lean
constant f : Nat → String
constant g : String → Bool
constant b : Bool

#check fun x : Nat => x        -- Nat → Nat
#check fun x : Nat => b        -- Nat → Bool
#check fun x : Nat => g (f x)  -- Nat → Bool
#check fun x => g (f x)        -- Nat → Bool
```

Think about what these expressions mean. The expression ``fun x : Nat => x`` denotes the identity function on ``Nat``,
the expression ``fun x : α => b`` denotes the constant function that always returns ``b``,
and ``fun x : Nat => g (f x)``, denotes the composition of ``f`` and ``g``.
We can, in general, leave off the type annotation on a variable and let Lean infer it for us.
So, for example, we can write ``fun x => g (f x)`` instead of ``fun x : Nat => g (f x)``.

We can abstract over the constants `f` and `g` in the previous definitions:

```lean
#check fun (g : String → Bool) (f : Nat → String) (x : Nat) => g (f x)
-- (String → Bool) → (Nat → String) → Nat → Bool
```

We can also abstract over types:

```lean
#check fun (α β γ : Type) (g : β → γ) (f : α → β) (x : α) => g (f x)
```
The last expression, for example, denotes the function that takes three types, ``α``, ``β``, and ``γ``, and two functions, ``g : β → γ`` and ``f : α → β``, and returns the composition of ``g`` and ``f``. (Making sense of the type of this function requires an understanding of dependent products, which we will explain below.) Within a lambda expression ``fun x : α => t``, the variable ``x`` is a "bound variable": it is really a placeholder, whose "scope" does not extend beyond ``t``.
For example, the variable ``b`` in the expression ``fun (b : β) (x : α) => b`` has nothing to do with the constant ``b`` declared earlier.
In fact, the expression denotes the same function as ``fun (u : β) (z : α), u``. Formally, the expressions that are the same up to a renaming of bound variables are called *alpha equivalent*, and are considered "the same." Lean recognizes this equivalence.

Notice that applying a term ``t : α → β`` to a term ``s : α`` yields an expression ``t s : β``.
Returning to the previous example and renaming bound variables for clarity, notice the types of the following expressions:

```lean
#check (fun x : Nat => x) 1     -- Nat
#check (fun x : Nat => true) 1  -- Bool

constant f : Nat → String
constant g : String → Bool

#check
  (fun (α β γ : Type) (g : β → γ) (f : α → β) (x : α) => g (f x)) Nat String Bool g f 0
  -- Bool
```

As expected, the expression ``(fun x : Nat =>  x) 1`` has type ``Nat``.
In fact, more should be true: applying the expression ``(fun x : Nat => x)`` to ``1`` should "return" the value ``1``. And, indeed, it does:

```lean
#reduce (fun x : Nat => x) 1     -- 1
#reduce (fun x : Nat => true) 1  -- true

constant f : Nat → String
constant g : String → Bool

#reduce
  (fun (α β γ : Type) (g : β → γ) (f : α → β) (x : α) => g (f x)) Nat String Bool g f 0
  -- g (f 0)
```

The command ``#reduce`` tells Lean to evaluate an expression by *reducing* it to its normal form,
which is to say, carrying out all the computational reductions that are sanctioned by its kernel.
The process of simplifying an expression ``(fun x => t) s`` to ``t[s/x]`` -- that is, ``t`` with ``s`` substituted for the variable ``x`` --
is known as *beta reduction*, and two terms that beta reduce to a common term are called *beta equivalent*.
But the ``#reduce`` command carries out other forms of reduction as well:

```lean
constant m : Nat
constant n : Nat
constant b : Bool

#reduce (m, n).1        -- m
#reduce (m, n).2        -- n

#reduce true && false   -- false
#reduce false && b      -- false
#reduce b && false      -- Bool.rec false false b

#reduce n + 0           -- n
#reduce n + 2           -- Nat.succ (Nat.succ n)
#reduce 2 + 3           -- 5
```

We explain later how these terms are evaluated.
For now, we only wish to emphasize that this is an important feature of dependent type theory:
every term has a computational behavior, and supports a notion of reduction, or *normalization*.
In principle, two terms that reduce to the same value are called *definitionally equal*.
They are considered "the same" by Lean's type checker, and Lean does its best to recognize and support these identifications.
The `#reduce` command is mainly useful to understand why two terms are considered the same.

Lean is also a programming language. It has a compiler to native code and an interpreter.
You can use the command `#eval` to execute expressions, and it is the preferred way of testing your functions.
Note that `#eval` and `#reduce` are *not* equivalent. The command `#eval` first compiles Lean expressions
into an intermediate representation (IR) and then uses an interpreter to execute the generated IR.
Some builtin types (e.g., `Nat`, `String`, `Array`) have a more efficient representation in the IR.
The IR has support for using foreign functions that are opaque to Lean.

In contrast, the ``#reduce`` command relies on a reduction engine similar to the one used in Lean's trusted kernel,
the part of Lean that is responsible for checking and verifying the correctness of expressions and proofs.
It is less efficient than ``#eval``, and treats all foreign functions as opaque constants.
We later discuss other differences between the two commands.

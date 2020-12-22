## Simple Type Theory

"Type theory" gets its name from the fact that every expression has an associated *type*.
For example, in a given context, ``x + 0`` may denote a natural number and ``f`` may denote a function on the natural numbers.
For those that don't like math, a Lean natural number is an arbitrary-precision unsigned integer.

Here are some examples of how we can declare objects in Lean and check their types.

```lean
/- Declare some constants. -/

constant m  : Nat   -- m is a natural number
constant n  : Nat
constant b1 : Bool  -- b1 is a Boolean
constant b2 : Bool

/- Check their types. -/

#check m            -- output: Nat
#check n
#check n + 0        -- Nat
#check m * (n + 0)  -- Nat
#check b1           -- Bool
#check b1 && b2     -- "&&" is the Boolean and
#check b1 || b2     -- Boolean or
#check true         -- Boolean "true"
```

Any text between ``/-`` and ``-/`` constitutes a comment block that is ignored by Lean.
Similarly, two dashes `--` indicate that the rest of the line contains a comment that is also ignored.
Comment blocks can be nested, making it possible to "comment out" chunks of code, just as in many programming languages.

The ``constant`` command introduce new constant symbols into the working environment.
The ``#check`` command asks Lean to report their types; in Lean, auxiliary commands that query the system for
information typically begin with the hash symbol. You should try declaring some constants and type checking
some expressions on your own. Declaring new objects in this way is a good way to experiment with the system.

What makes simple type theory powerful is that one can build new types out of others.
For example, if ``a`` and ``b`` are types, ``a -> b`` denotes the type of functions from ``a`` to ``b``,
and ``a × b`` denotes the type of pairs consisting of an element of ``a``
paired with an element of ``b``, also known as the *Cartesian product*.
Note that `×` is a Unicode symbol. We believe that judicious use of Unicode improves legibility,
and all modern editors have great support for it. In the Lean standard library, we often use
Greek letters to denote types, and the Unicode symbol `→` as a more compact version of `->`.

```lean
constant m : Nat
constant n : Nat

constant f  : Nat → Nat         -- type the arrow as "\to" or "\r"
constant f' : Nat -> Nat        -- alternative ASCII notation
constant p  : Nat × Nat         -- type the product as "\times"
constant q  : Prod Nat Nat      -- alternative notation
constant g  : Nat → Nat → Nat
constant g' : Nat → (Nat → Nat) -- has the same type as g!
constant h  : Nat × Nat → Nat
constant F  : (Nat → Nat) → Nat -- a "functional"

#check f            -- Nat → Nat
#check f n          -- Nat
#check g m n        -- Nat
#check g m          -- Nat → Nat
#check (m, n)       -- Nat × Nat
#check p.1          -- Nat
#check p.2          -- Nat
#check (m, n).1     -- Nat
#check (p.1, n)     -- Nat × Nat
#check F f          -- Nat
```

Once again, you should try some examples on your own.

Let us dispense with some basic syntax. You can enter the unicode arrow ``→`` by typing ``\to`` or ``\r``.
You can also use the ASCII alternative ``->``, so the expressions ``Nat -> Nat`` and ``Nat → Nat`` mean the same thing.
Both expressions denote the type of functions that take a natural number as input and return a natural number as output.
The unicode symbol ``×`` for the Cartesian product is entered as ``\times``.
We will generally use lower-case Greek letters like ``α``, ``β``, and ``γ`` to range over types.
You can enter these particular ones with ``\a``, ``\b``, and ``\g``.

There are a few more things to notice here. First, the application of a function ``f`` to a value ``x`` is denoted ``f x``.
Second, when writing type expressions, arrows associate to the *right*; for example, the type of ``g`` is ``Nat → (Nat → Nat)``.
Thus we can view ``g`` as a function that takes natural numbers and returns another function that takes a natural number and
returns a natural number.
In type theory, this is generally more convenient than writing ``g`` as a function that takes a pair of natural numbers as input
and returns a natural number as output. For example, it allows us to "partially apply" the function ``g``.
The example above shows that ``g m`` has type ``Nat → Nat``, that is, the function that "waits" for a second argument, ``n``,
and then returns ``g m n``. Taking a function ``h`` of type ``Nat × Nat → Nat`` and "redefining" it to look like ``g`` is a process
known as *currying*, something we will come back to below.

By now you may also have guessed that, in Lean, ``(m, n)`` denotes the ordered pair of ``m`` and ``n``,
and if ``p`` is a pair, ``p.1`` and ``p.2`` denote the two projections.

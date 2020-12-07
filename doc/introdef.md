## Introducing Definitions

The ``def`` command provides one important way of defining new objects.

```lean

def foo : (Nat → Nat) → Nat :=
  fun f => f 0

#check foo   -- (Nat → Nat) → Nat
#print foo
```

We can omit the type when Lean has enough information to infer it:

```lean
def foo :=
  fun (f : Nat → Nat) => f 0
```

The general form of a definition is ``def foo : α := bar``. Lean can usually infer the type ``α``, but it is often a good idea to write it explicitly.
This clarifies your intention, and Lean will flag an error if the right-hand side of the definition does not have the right type.

Lean also allows us to use an alternative format that puts the abstracted variables before the colon and omits the lambda:
```lean
def double (x : Nat) : Nat :=
  x + x

#print double
#check double 3
#reduce double 3  -- 6
#eval double 3    -- 6

def square (x : Nat) :=
  x * x

#print square
#check square 3
#reduce square 3  -- 9
#eval square 3    -- 9

def doTwice (f : Nat → Nat) (x : Nat) : Nat :=
  f (f x)

#eval doTwice double 2   -- 8
```

These definitions are equivalent to the following:

```lean
def double : Nat → Nat :=
  fun x => x + x

def square : Nat → Nat :=
  fun x => x * x

def doTwice : (Nat → Nat) → Nat → Nat :=
  fun f x => f (f x)
```

We can even use this approach to specify arguments that are types:

```lean
def compose (α β γ : Type) (g : β → γ) (f : α → β) (x : α) : γ :=
  g (f x)
```

# Structures

Structure is a special case of inductive datatype. It has only one constructor and is not recursive.
Similar to the `inductive` command, the `structure` command introduces a namespace with the same name.
The general form is as follows:
```
structure <name> <parameters> <parent-structures> where
  <constructor-name> :: <fields>
```
Most parts are optional. Here is our first example.
```lean
structure Point (α : Type u) where
  x : α
  y : α
```
In the example above, the constructor name is not provided. So, the constructor is named `mk` by Lean.
Values of type ``Point`` are created using `Point.mk a b` or `{ x := a, y := b : Point α }`. The latter can be
written as `{ x := a, y := b }` when the expected type is known.
The fields of a point ``p`` are accessed using ``Point.x p`` and ``Point.y p``. You can also the more compact notation `p.x` and `p.y` as a shorthand
for `Point.x p` and `Point.y p`.
```lean
# structure Point (α : Type u) where
#  x : α
#  y : α
#check Point
#check Point       -- Type u -> Type u
#check @Point.mk   -- {α : Type u} → α → α → Point α
#check @Point.x    -- {α : Type u} → Point α → α
#check @Point.y    -- {α : Type u} → Point α → α

#check Point.mk 10 20                   -- Point Nat
#check { x := 10, y := 20 : Point Nat } -- Point Nat

def mkPoint (a : Nat) : Point Nat :=
  { x := a, y := a }

#eval (Point.mk 10 20).x                   -- 10
#eval (Point.mk 10 20).y                   -- 20
#eval { x := 10, y := 20 : Point Nat }.x   -- 10
#eval { x := 10, y := 20 : Point Nat }.y   -- 20

def addXY (p : Point Nat) : Nat :=
  p.x + p.y

#eval addXY { x := 10, y := 20 }    -- 30
```
In the notation `{ ... }`, if the fields are in different lines, the `,` is optional.
```lean
# structure Point (α : Type u) where
#  x : α
#  y : α
def mkPoint (a : Nat) : Point Nat := {
  x := a
  y := a
}
```
You can also use `where` instead of `:= { ... }`.
```lean
# structure Point (α : Type u) where
#  x : α
#  y : α
def mkPoint (a : Nat) : Point Nat where
  x := a
  y := a
```

Here are some simple theorems about our `Point` type.
```lean
# structure Point (α : Type u) where
#  x : α
#  y : α
theorem ex1 (a b : α) : (Point.mk a b).x = a :=
  rfl

theorem ex2 (a b : α) : (Point.mk a b).y = b :=
  rfl

theorem ex3 (a b : α) : Point.mk a b = { x := a, y := b } :=
  rfl
```

The dot notation is convenient not just for accessing the projections of a structure,
but also for applying functions defined in a namespace with the same name.
If ``p`` has type ``Point``, the expression ``p.foo`` is interpreted as ``Point.foo p``,
assuming that the first argument to ``foo`` has type ``Point``.
The expression ``p.add q`` is therefore shorthand for ``Point.add p q`` in the example below.
```lean
structure Point (α : Type u) where
  x : α
  y : α

def Point.add (p q : Point Nat) : Point Nat :=
  { x := p.x + q.x, y := p.y + q.y }

def p : Point Nat := Point.mk 1 2
def q : Point Nat := Point.mk 3 4

#eval (p.add q).x  -- 4
#eval (p.add q).y  -- 6
```

After we introduce type classes, we show how to define a function like ``add`` so that
it works generically for elements of ``Point α`` rather than just ``Point Nat``,
assuming ``α`` has an associated addition operation.

More generally, given an expression ``p.foo x y z``, Lean will insert ``p`` at the first argument to ``foo`` of type ``Point``.
For example, with the definition of scalar multiplication below, ``p.smul 3`` is interpreted as ``Point.smul 3 p``.

```lean
structure Point (α : Type u) where
  x : α
  y : α

def Point.smul (n : Nat) (p : Point Nat) :=
  Point.mk (n * p.x) (n * p.y)

def p : Point Nat :=
  Point.mk 1 2

#eval (p.smul 3).x -- 3
#eval (p.smul 3).y -- 6
```

##  Inheritance

We can *extend* existing structures by adding new fields. This feature allows us to simulate a form of *inheritance*.

```lean
structure Point (α : Type u) where
  x : α
  y : α

inductive Color where
  | red
  | green
  | blue

structure ColorPoint (α : Type u) extends Point α where
  color : Color

#check { x := 10, y := 20, color := Color.red : ColorPoint Nat }
-- { toPoint := { x := 10, y := 20 }, color := Color.red }
```
The output for the `check` command above suggests how Lean encoded inheritance and multiple inheritance.
Lean uses fields to each parent structure.

```lean
structure Foo where
  x : Nat
  y : Nat

structure Boo where
  w : Nat
  z : Nat

structure Bla extends Foo, Boo where
  bit : Bool

#check Bla.mk -- Foo → Boo → Bool → Bla
#check Bla.mk { x := 10, y := 20 } { w := 30, z := 40 } true
#check { x := 10, y := 20, w := 30, z := 40, bit := true : Bla }
#check { toFoo := { x := 10, y := 20 },
         toBoo := { w := 30, z := 40 },
         bit := true : Bla }

theorem ex :
    Bla.mk { x := x, y := y } { w := w, z := z } b
    =
    { x := x, y := y, w := w, z := z, bit := b } :=
  rfl
```

## Default field values

You can assign default value to fields when declaring a new structure.
```lean
inductive MessageSeverity
  | error | warning

structure Message where
  fileName : String
  pos      : Option Nat      := none
  severity : MessageSeverity := MessageSeverity.error
  caption  : String          := ""
  data     : String

def msg1 : Message :=
  { fileName := "foo.lean", data := "failed to import file" }

#eval msg1.pos      -- none
#eval msg1.fileName -- "foo.lean"
#eval msg1.caption  -- ""
```
When extending a structure, you can not only add new fields, but provide new default values for existing fields.
```lean
# inductive MessageSeverity
#  | error | warning
# structure Message where
#  fileName : String
#  pos      : Option Nat      := none
#  severity : MessageSeverity := MessageSeverity.error
#  caption  : String          := ""
#  data     : String
structure MessageExt extends Message where
  timestamp : Nat
  caption   := "extended" -- new default value for field `caption`

def msg2 : MessageExt where
  fileName  := "bar.lean"
  data      := "error at initialization"
  timestamp := 10

#eval msg2.fileName  -- "bar.lean"
#eval msg2.timestamp -- 10
#eval msg2.caption   -- "extended"
```

## Updating structure fields

TODO
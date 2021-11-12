# Types

Every programming language needs a type system and
Lean has a rich extensible inductive type system.

## Basic Types

Lean has built in support for the following basic types:

- [Bool](bool.md) : a `true` or `false` value.
- [Int](integers.md) : multiple precision integers (with no overflows!).

- [Nat](integers.md) : natural numbers, or non-negative integers (also with no overflows!).
- [Float](float.md): floating point numbers.
- [Char](char.md): a Unicode character.
- [String](string.md): a UTF-8 encoded string of characters.
- [Array](array.md): a dynamic (aka growable) array of typed objects.
- [List](list.md): a linked list of typed objects.
- TODO: what else?

And Lean allows you to create your own custom types using:
- [Enumerated Types](enum.md): a special case of inductive types.
- [Type Classes](typeclasses.md): a way of creating custom polymorphism.
- [Types as objects](typeobjs.md): a way of manipulating types themselves.
- [Structures](struct.md): a collection of named and typed fields. A
  structure is actually special case of inductive datatype.
- [Inductive Types](inductive.md): TODO: add one liner...

## Universes

Every type in Lean is, by definition, an expression of type `Sort u`
for some universe level `u`. A universe level is one of the
following:

* a natural number, `n`
* a universe variable, `u` (declared with the command `universe` or `universes`)
* an expression `u + n`, where `u` is a universe level and `n` is a natural number
* an expression `max u v`, where `u` and `v` are universes
* an expression `imax u v`, where `u` and `v` are universe levels

The last one denotes the universe level `0` if `v` is `0`, and `max u v` otherwise.

```lean
universe u v

#check Sort u                       -- Type u
#check Sort 5                       -- Type 4 : Type 5
#check Sort (u + 1)                 -- Type u : Type (u + 1)
#check Sort (u + 3)                 -- Type (u + 2) : Type (u + 3)
#check Sort (max u v)               -- Sort (max u v) : Type (max u v)
#check Sort (max (u + 3) v)         -- Sort (max (u + 3) v) : Type (max (u + 3) v)
#check Sort (imax (u + 3) v)        -- Sort (imax (u + 3) v) : Type (imax (u + 3) v)
#check Prop                         -- Type
#check Type                         -- Type 1
#check Type 1                       -- Type 1 : Type 2
```

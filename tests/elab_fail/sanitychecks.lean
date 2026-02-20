theorem unsound : False := -- Error
  unsound

partial theorem unsound2 : False := -- Error
  unsound2

unsafe theorem unsound3 : False := -- Error
  unsound3

opaque unsound4 : False  -- Error

axiom magic : False -- OK
namespace Foo
partial def foo (x : Nat) : Nat := foo x  -- OK

unsafe def unsound2 : False := unsound  -- OK

partial def unsound3 : False := unsound3  -- Error

partial def unsound4 (x : Unit) : False := unsound4 ()  -- Error

partial def badcast1 (x : Nat) : Bool :=
  unsafeCast x -- Error: partial cannot use unsafe constant

partial def badcast2 (x : Nat) : Bool :=
  if x == 0 then unsafeCast x -- Error: partial cannot use unsafe constant
  else badcast2 (x + 1)

unsafe def badcast3 (x : Nat) : Bool := -- OK
  if x == 0 then unsafeCast x
  else badcast3 (x + 1)

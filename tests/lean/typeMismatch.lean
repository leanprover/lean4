import Lean


-- Test type mismatch error messages for "liftable" methods

def test (x : Nat) : IO Nat :=
IO.println ""

open Lean

def test (x : Expr) : MetaM Unit :=
Meta.isDefEq x x

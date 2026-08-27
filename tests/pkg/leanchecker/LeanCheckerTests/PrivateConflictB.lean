module

prelude
public import Init.Core

public def foo : Nat := 23

public theorem thm2 : True := if foo = 23 then trivial else trivial

@[extern]
def foo (x : Nat) := x

@[extern "bla"]
def foo2 (x : Nat) := x

@[extern 2 "boo"]
def foo3 (x : Nat) := x

@[extern cpp "Lean::bla" llvm "lean_bla"]
def foo4 (x : Bool) := x

@[extern cpp inline "#1 && #2"]
def foo5 (x y : Bool) := x

-- @[extern cpp adhoc llvm "foo"]
-- def foo6 (x y : Bool) := x

@[extern]
def foo (x : nat) := x

@[extern "bla"]
def foo2 (x : nat) := x

@[extern 2 "boo"]
def foo3 (x : nat) := x

@[extern cpp "lean::bla" llvm "lean_bla"]
def foo4 (x : bool) := x

@[extern cpp inline "#1 && #2"]
def foo5 (x y : bool) := x

@[extern cpp adhoc llvm "foo"]
def foo6 (x y : bool) := x

namespace ns

structure struct :=
(index : ℕ)

end ns

open ns

def foo : struct :=
{ ns.struct . index := 1 }

def foo2 : struct :=
{ struct . index := 1 }

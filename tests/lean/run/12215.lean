set_option trace.Meta.MkIffOfInductiveProp true

namespace test1
coinductive Foo : {n : Nat} → Fin n → Prop
| succ {m : Nat} (x : Fin (m + 1)) : Foo x
| one (x : Fin 1) : Foo x
end test1

namespace test2
coinductive Foo : (n : Nat) → Fin n → Prop
| succ {m : Nat} (x : Fin (m + 1)) : Foo (m+1) x
| one (x : Fin 1) : Foo 1 x
end test2

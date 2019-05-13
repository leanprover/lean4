import init.lean.smap

abbrev Map : Type := Lean.SMap Nat Bool (λ a b, a < b)

@[extern "lean_smap_foreach_test"]
constant foreachTest : Map → Nat := default _

def test1 (n₁ n₂ : Nat) : IO Unit :=
let m : Map := {} in
let m := n₁.fold (λ i (m : Map), m.insert i (i % 2 == 0)) m in
let m := m.switch in
let m := n₂.fold (λ i (m : Map), m.insert (i+n₁) (i % 3 == 0)) m in
do
IO.println (foreachTest m),
n₁.mfor $ λ i, IO.println (i, (m.find i)),
n₂.mfor $ λ i, IO.println (i+n₁, (m.find (i+n₁))),
IO.println (m.foldStage2 (λ kvs k v, (k, v)::kvs) [])

def main (xs : List String) : IO Unit :=
test1 xs.head.toNat xs.tail.head.toNat

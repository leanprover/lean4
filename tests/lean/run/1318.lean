def tester : Π (n : ℕ) (e : fin n), true -- fails : "infer type failed, unknown variable m"
| 0 e := trivial
| (m+1) (fin.mk 0 lt) := trivial
| (m+1) (fin.mk (k+1) lt) := trivial

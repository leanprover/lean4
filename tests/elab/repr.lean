--

def iota (n : Nat) := List.range' 1 n |>.reverse

#eval repr (1, 2, 3)
#eval repr (some 1, some (some true))
#eval iota 10 |>.map some |>.map some
#eval iota 15 |>.map fun x => (x, some x)
#eval repr ("hello", 1, true, false, 'a', "testing tuples", "another string", "another string", "testing bigger tuples that should not fit in a single line", 20)
#eval iota 50 |>.toArray
#eval iota 20 |>.map fun i => if i % 2 == 0 then Except.ok (some i) else Except.error "no even"

instance : ReprAtom (Except String (Option Nat)) := ⟨⟩

#eval iota 20 |>.map fun i => if i % 2 == 0 then Except.ok (some i) else Except.error "no even"

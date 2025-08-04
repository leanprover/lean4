--

#eval repr (1, 2, 3)
#eval repr (some 1, some (some true))
#eval List.range 10 |>.reverse |>.map some |>.map some
#eval List.range 15 |>.reverse |>.map fun x => (x, some x)
#eval repr ("hello", 1, true, false, 'a', "testing tuples", "another string", "another string", "testing bigger tuples that should not fit in a single line", 20)
#eval List.range 50 |>.reverse |>.toArray
#eval List.range 20 |>.reverse |>.map fun i => if i % 2 == 0 then Except.ok (some i) else Except.error "no even"

instance : ReprAtom (Except String (Option Nat)) := ⟨⟩

#eval List.range 20 |>.reverse |>.map fun i => if i % 2 == 0 then Except.ok (some i) else Except.error "no even"

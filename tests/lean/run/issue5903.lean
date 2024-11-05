def foo (n : Nat) (_h : True) : Nat :=
  n

def bar : Nat → { _n : Nat // True }
  | 0 => ⟨0, trivial⟩
  | n + 1 =>
      let r := bar n
      ⟨foo r.1 r.2, trivial⟩

def bar_induct := @bar.induct

/-!
Tests that `simp` does not reuse a cached result whose proof mentions a hypothesis that `simp`
introduced itself while descending into a term (here the `h` of the `dite`). Reusing such a result
in a sibling branch produced a proof with free variables, which the kernel rejects.
-/

def f (n : Nat) : Nat :=
  if _h : n = 0 then 0 else (let s := n; match s, true with | 2, false => 1 | _, _ => 0) + f 0
  termination_by n

example (n : Nat) :
    (if _h : n = 0 then (let s := n; match s, true with | 2, false => 1 | _, _ => 0)
     else (let s := n; match s, true with | 2, false => 1 | _, _ => 0)) = 0 := by
  simp

/-!
Regression test for #15822: the smart unfolding definition of a function defined by mutual
structural recursion only marked the `match`es containing recursive calls to the function itself,
not those containing calls to the other functions of the group. So `dsimp only [f]` unfolded
`f` even when an inner `match` did not reduce, producing a non-definitional rewrite that the
kernel rejected.
-/

inductive T where
  | leaf : T
  | node : List T → T

mutual
def f : T → Nat
  | .node [_, t] =>
      match t with
      | .node [u] => g u
      | _ => 0
  | _ => 0
def g : T → Nat
  | .node [t] => f t
  | _ => 0
end

/-- error: `dsimp` made no progress -/
#guard_msgs in
theorem bad (a t : T) (h : f (.node [a, t]) = 0) :
    (match (generalizing := false) t with | .node [u] => g u | _ => 0) = 0 := by
  dsimp only [f] at h
  exact h

theorem good (a t : T) (h : f (.node [a, t]) = 0) :
    (match (generalizing := false) t with | .node [u] => g u | _ => 0) = 0 := by
  unfold f at h
  exact h

-- Smart unfolding still fires when the inner `match` reduces.
example (a u : T) (h : f (.node [a, .node [u]]) = 0) : g u = 0 := by
  dsimp only [f] at h
  exact h

-- And for calls to the other function directly under the outer `match`.
mutual
def ev : Nat → Bool
  | 0 => true
  | n+1 => od n
def od : Nat → Bool
  | 0 => false
  | n+1 => ev n
end

example (x : Nat) (h : ev (x + 1) = true) : od x = true := by
  dsimp only [ev] at h
  exact h

/-- error: `dsimp` made no progress -/
#guard_msgs in
example (x : Nat) (h : ev x = true) : True := by
  dsimp only [ev] at h
  trivial

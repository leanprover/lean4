/--
error: tactic 'fail' failed
x y : Nat
⊢ x - 1 < x
-/
#guard_msgs in
def g (x : Nat) (y : Nat) : Nat := g (x - 1) y
termination_by x
decreasing_by fail

/--
error: tactic 'fail' failed
x : List Nat
y : Nat
⊢ sizeOf x.tail < sizeOf x
-/
#guard_msgs in
def h (x : List Nat) (y : Nat) : Nat := h x.tail y
termination_by x
decreasing_by fail

/--
error: tactic 'fail' failed
x : List Nat
y : Nat
⊢ x.tail.length < x.length
-/
#guard_msgs in
def f (x : List Nat) (y : Nat) : Nat := f x.tail y
termination_by x.length
decreasing_by fail

/--
error: tactic 'fail' failed
x : List Nat
y : Nat
⊢ x.tail.length < x.length
-/
#guard_msgs in
mutual
def f1 (x : List Nat) (y : Nat) : Nat := f2 x.tail y
termination_by x.length
decreasing_by fail
def f2 (x : List Nat) (y : Nat) : Nat := f1 x.tail y
termination_by x.length
decreasing_by fail
end

/--
error: tactic 'fail' failed
x : List Nat
y : Nat
⊢ (invImage
        (fun x =>
          PSum.casesOn x (fun _x => PSigma.casesOn _x fun x y => x.length) fun _x =>
            PSigma.casesOn _x fun x y => x.length)
        instWellFoundedRelationOfSizeOf).1
    (PSum.inr ⟨x.tail, y⟩) (PSum.inl ⟨x, y⟩)
-/
#guard_msgs in
set_option debug.rawDecreasingByGoal true in
mutual
def g1 (x : List Nat) (y : Nat) : Nat := g2 x.tail y
termination_by x.length
decreasing_by fail
def g2 (x : List Nat) (y : Nat) : Nat := g1 x.tail y
termination_by x.length
decreasing_by fail
end

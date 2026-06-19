/-!
Regression tests for issue #13729.

After PR #7166, `termination_by structural` runs the structural-recursion
analysis on parameters reordered with `FixedParamPerm.buildArgs xs ys`, so
`recArgInfo.recArgPos` indexes into that array (the original parameter
order). Three places in `FindRecArg.lean` instead concatenated `xs ++ ys`
(fixed parameters first) and dereferenced with `recArgPos`, picking the
wrong element whenever fixed and varying parameters were interleaved.
-/

inductive Tree where
  | leaf : Tree
  | node : Tree → Tree → Tree

/--
error: failed to infer structural recursion:
Cannot use parameter h:
  failed to eliminate recursive application
    test (m + 1) (h.node h) c
-/
#guard_msgs in
def test (m : Nat) (h : Tree) (c : Bool) : Nat :=
  match h with
  | .leaf => m
  | .node _ _ => test (m+1) (Tree.node h h) c
termination_by structural h

/-!
Nested-inductive case exercising the same bug in
`argsInGroup` (the second/third occurrences). `Tree₂.sizeList`'s structural
argument has type `List Tree₂` while the relevant inductive group is `Tree₂`,
so `argsInGroup` must recognize the argument as a nested type former. Picking
the wrong element of the parameter array (i.e. `c` instead of `ts`) would make
that recognition fail and reject the definition.
-/

inductive Tree₂ where
  | node : List Tree₂ → Tree₂

mutual
def Tree₂.size (m : Nat) (t : Tree₂) (c : Bool) : Nat :=
  match t with
  | .node ts => Tree₂.sizeList m ts c + 1
  termination_by structural t

def Tree₂.sizeList (m : Nat) (ts : List Tree₂) (c : Bool) : Nat :=
  match ts with
  | [] => 0
  | t :: rest => Tree₂.size m t c + Tree₂.sizeList m rest c
  termination_by structural ts
end

/-- info: 4 -/
#guard_msgs in
#eval Tree₂.size 0 (.node [.node [], .node [.node []]]) true

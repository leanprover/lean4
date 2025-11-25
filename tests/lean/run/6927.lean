import Lean
/-
# Nested `let rec` declarations in the presence of delayed metavariable assignments

https://github.com/leanprover/lean4/issues/6927

Nested declarations using `let rec` should compile correctly even when nested within expressions
that are elaborated using delayed metavariable assignments, such as `match` expressions and tactic
blocks. See the Note [Delayed-Assigned Metavariables in Free Variable Collection] in
`MutualDef.lean` for additional details.
-/

inductive Tree : Type where
  | leaf
  | node (p : Nat) (brs : List Tree)
def Tree.substNats (M : Tree) (σ : Nat → Nat) : Tree :=
  let rec go M : Tree := match M with
    | .leaf => leaf
    | .node p brs =>
      let rec goList : List Tree → List Tree
        | [] => []
        | M :: Ms => go M :: goList Ms
      .node (σ p) (goList brs)
  go M


/-
Previously, free variable dependencies in `inner` were not correctly detected, leading that
declaration to contain free variables when sent to the kernel.
-/
namespace Ex1
def outer (f : Nat → Nat) :=
  let rec middle n := match n with
  | Nat.zero => 0 | .succ _ =>
    let rec inner := middle n
    f 0
  ()
end Ex1

/-
`by` blocks induced behavior similar to the above, since they also produce metavariables during
elaboration.
-/
def tac (f : Nat → Nat) :=
  let rec middle n := by
    let rec inner := middle (Nat.succ n)
    exact f 0
  ()

/- Previously, `inner` was incorrectly compiled as an `axiom`, rendering `outer` noncomputable. -/
namespace Ex2
/--
error: fail to show termination for
  Ex2.outer.middle.inner
  Ex2.outer.middle
with errors
failed to infer structural recursion:
Not considering parameter f of Ex2.outer.middle.inner:
  it is unchanged in the recursive calls
Not considering parameter f of Ex2.outer.middle:
  it is unchanged in the recursive calls
Cannot use parameters n✝ of Ex2.outer.middle.inner and n of Ex2.outer.middle:
  failed to eliminate recursive application
    outer.middle f✝ (n + 1)
Cannot use parameters n of Ex2.outer.middle.inner and n of Ex2.outer.middle:
  failed to eliminate recursive application
    outer.middle f✝ (n + 1)


Could not find a decreasing measure.
The basic measures relate at each recursive call as follows:
(<, ≤, =: relation proved, ? all proofs failed, _: no proof attempted)
Call from Ex2.outer.middle.inner to Ex2.outer.middle at 89:6-20:
  n✝ n
n  ? ?
Call from Ex2.outer.middle to Ex2.outer.middle.inner at 91:4-11:
   n
n✝ _
n  _

Please use `termination_by` to specify a decreasing measure.
-/
#guard_msgs in
def outer (f : Nat → Nat) (n : Nat) : Nat :=
  let rec middle n : Nat := match n with
  | 0 => 1
  | n + 1 =>
    let rec inner (n : Nat) : Nat :=
      middle (n + 1)
    let _ := f
    inner n
  middle n
end Ex2

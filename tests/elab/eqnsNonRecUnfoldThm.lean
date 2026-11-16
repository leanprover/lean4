import Lean
/-!
The equation theorems of a nonrecursive definition unfold the definition using `f.eq_def`.

They used to be `id (f a = rhs) h` with `h : body[a] = rhs`, and the kernel had to check
`f a =?= body[a]`. When the body is a `match` on values and `a` is a literal, the kernel evaluated
the `match` (`String.decEq` on literals) instead of unfolding `f`: the matcher has `abbrev`
reducibility hints, and `f` does not have greater definitional height than `dite`.
-/
open Lean Meta

def f : String → Nat
  | "a" => 0
  | "b" => 1
  | _ => 2

def g (x : Nat) (s : String) : Nat :=
  match x, s with
  | 0, "a" => 0
  | 1, "b" => 1
  | _, _ => x

/-- Checks that the proof of each equation theorem of `declName` is `Eq.trans (declName.eq_def ..) ..`. -/
def checkEqns (declName : Name) : MetaM Unit := do
  let some eqns ← getEqnsFor? declName | throwError "no equations for `{declName}`"
  for eqn in eqns do
    let .thmInfo info ← getConstInfo eqn | throwError "theorem expected"
    forallTelescope info.type fun xs _ => do
      let proof := info.value.beta xs
      let_expr Eq.trans _ _ _ _ h _ := proof
        | throwError "`{eqn}`: unexpected proof{indentExpr proof}"
      unless h.isAppOf (declName ++ `eq_def) do
        throwError "`{eqn}`: unexpected proof{indentExpr proof}"

run_meta checkEqns ``f
run_meta checkEqns ``g

/-- info: f.eq_2 : f "b" = 1 -/
#guard_msgs in
#check f.eq_2

/--
info: g.eq_3 (x : Nat) (s : String) (x_4 : x = 0 → s = "a" → False) (x_5 : x = 1 → s = "b" → False) : g x s = x
-/
#guard_msgs in
#check g.eq_3

example : f "b" = 1 := by simp [f]
example : g 1 "b" = 1 := by simp [g]

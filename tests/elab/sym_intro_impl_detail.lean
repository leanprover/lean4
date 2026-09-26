import Lean
import Std.WP
import Std.Tactic.Do

/-!
`Sym.intros` introduces a binder whose name starts with `__` as an implementation-detail local,
as the elaborator does for such binders (`LocalDeclKind.ofBinderName`). `vcgen` introduces the join
point `__do_jp` of a `do` block with `Sym.intros`, so its VCs then hide the join point.
-/

open Lean Meta Sym in
/--
info: __x: implDetail=true
__y: implDetail=true
z: implDetail=false
-/
#guard_msgs in
#eval show MetaM Unit from do
  let ty ← mkForallFVars #[] <| .forallE `__x (mkConst ``Nat)
    (.letE `__y (mkConst ``Nat) (mkNatLit 1)
      (.forallE `z (mkConst ``Nat) (mkConst ``True) .default) false) .default
  let goal ← mkFreshExprMVar ty .syntheticOpaque
  let .goal fvars goal ← Sym.SymM.run (Sym.intros goal.mvarId! #[`__x, `__y, `z])
    | throwError "intros failed"
  goal.withContext do
    for fvar in fvars do
      let decl ← fvar.getDecl
      IO.println s!"{decl.userName}: implDetail={decl.isImplementationDetail}"

def f (n : Nat) : Id Nat := do
  let mut x := 0
  if n > 0 then x := 1 else x := 2
  return x + 1

set_option experimental.vcgen true in
/--
trace: case vc1
n : Nat
h✝ : 0 < n
⊢ 1 < 1 + 1
case vc2
n : Nat
h✝ : ¬0 < n
⊢ 1 < 2 + 1
-/
#guard_msgs in
open Std.WP in
example : ⦃ True ⦄ f n ⦃ fun r => r > 1 ⦄ := by
  unfold f
  vcgen
  all_goals trace_state
  all_goals omega

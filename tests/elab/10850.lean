module
public meta import Lean
/-!
# Testing `Lean.Meta.zetaReduce`

It needs to be able to reduce both `let` and `have` expressions.
Previously it was relying on the fact that `let` creates local definitions,
then zeta-delta reducing.
-/

open Lean Elab Term Meta Tactic

elab "zetaReduce " zd?:"zetaDelta"? zh?:"zetaHave"? beta?:"beta"? ":" t:term : tactic => withMainContext do
  let e ← elabTermAndSynthesize t none
  let e' ← zetaReduce e (zetaDelta := zd?.isSome) (zetaHave := zh?.isSome) (beta := beta?.isSome)
  logInfo m!"Before reduction:{indentExpr e}\nAfter reduction:{indentExpr e'}"

/--
info: Before reduction:
  (have m := 0 + 1;
    m - 1) =
    0
After reduction:
  (have m := 0 + 1;
    m - 1) =
    0
---
info: Before reduction:
  (have m := 0 + 1;
    m - 1) =
    0
After reduction:
  0 + 1 - 1 = 0
---
info: Before reduction:
  v
After reduction:
  v
---
info: Before reduction:
  v
After reduction:
  2
---
info: Before reduction:
  f v
After reduction:
  f v
---
info: Before reduction:
  f v
After reduction:
  (fun n =>
      have m := n;
      m + 1)
    2
---
info: Before reduction:
  f v
After reduction:
  have m := 2;
  m + 1
---
info: Before reduction:
  f v
After reduction:
  (fun n => n + 1) 2
---
info: Before reduction:
  f v
After reduction:
  2 + 1
---
error: unsolved goals
v : Nat := 2
f : Nat → Nat :=
  fun n =>
    have m := n;
    let m' := m;
    m' + 1
⊢ True
-/
#guard_msgs in
example : True := by
  let v := 2
  let f n := have m := n; let m' := m; m' + 1
  zetaReduce : (have m := 0 + 1; m - 1) = 0
  zetaReduce zetaHave : (have m := 0 + 1; m - 1) = 0
  zetaReduce : v
  zetaReduce zetaDelta : v
  zetaReduce : f v
  zetaReduce zetaDelta : f v
  zetaReduce zetaDelta beta : f v
  zetaReduce zetaDelta zetaHave : f v
  zetaReduce zetaDelta zetaHave beta : f v

import Lean
open Lean Expr Level -- just for shorter outpt

-- set_option trace.Meta.Match.match true
-- set_option trace.Meta.Match.debug true
-- set_option trace.Meta.Tactic.induction true

def simple : Lean.Expr → Bool
  | .sort _ => true
  | _      => false

/--
info: def simple.match_1.{u_1} : (motive : Expr → Sort u_1) →
  (x : Expr) → ((u : Level) → motive (sort u)) → ((x : Expr) → motive x) → motive x :=
fun motive x h_1 h_2 => simple._sparseCasesOn_1 x (fun u => h_1 u) fun h => h_2 x
-/
#guard_msgs in
#print simple.match_1

-- Check that the splitter re-uses the sparseCasesOn generated for the matcher:

/--
info: private def simple.match_1.splitter.{u_1} : (motive : Expr → Sort u_1) →
  (x : Expr) →
    ((u : Level) → motive (sort u)) → ((x : Expr) → (∀ (u : Level), x = sort u → False) → motive x) → motive x :=
fun motive x h_1 h_2 => simple._sparseCasesOn_1 x (fun u => h_1 u) fun h => h_2 x ⋯
-/
#guard_msgs in
#print simple.match_1.splitter

def expensive : Lean.Expr → Lean.Expr → Bool
  | .app (.app (.sort 1) (.sort 1)) (.sort 1), .app (.app (.sort 1) (.sort 1)) (.sort 1) => false
  | _, _ => true

/-- info: false -/
#guard_msgs in
#eval expensive (.app (.app (.sort 1) (.sort 1)) (.sort 1)) (.app (.app (.sort 1) (.sort 1)) (.sort 1))

/-- info: true -/
#guard_msgs in
#eval expensive (.app (.app (.sort 2) (.sort 1)) (.sort 1)) (.app (.app (.sort 1) (.sort 1)) (.sort 1))

example : expensive (.app (.app (.sort 1) (.sort 1)) (.sort 1)) (.app (.app (.sort 1) (.sort 1)) (.sort 1)) = false := rfl
example : expensive (.app (.app (.sort 2) (.sort 1)) (.sort 1)) (.app (.app (.sort 1) (.sort 1)) (.sort 1)) = true := rfl

/--
info: expensive.match_1.{u_1} (motive : Expr → Expr → Sort u_1) (x✝ x✝¹ : Expr)
  (h_1 :
    Unit →
      motive (((sort zero.succ).app (sort zero.succ)).app (sort zero.succ))
        (((sort zero.succ).app (sort zero.succ)).app (sort zero.succ)))
  (h_2 : (x x_1 : Expr) → motive x x_1) : motive x✝ x✝¹
-/
#guard_msgs in
#check expensive.match_1
/--
info: expensive.match_1.splitter.{u_1} (motive : Expr → Expr → Sort u_1) (x✝ x✝¹ : Expr)
  (h_1 :
    Unit →
      motive (((sort zero.succ).app (sort zero.succ)).app (sort zero.succ))
        (((sort zero.succ).app (sort zero.succ)).app (sort zero.succ)))
  (h_2 :
    (x x_1 : Expr) →
      (x = ((sort zero.succ).app (sort zero.succ)).app (sort zero.succ) →
          x_1 = ((sort zero.succ).app (sort zero.succ)).app (sort zero.succ) → False) →
        motive x x_1) :
  motive x✝ x✝¹
-/
#guard_msgs in
#check expensive.match_1.splitter

/--
info: expensive.match_1.eq_1.{u_1} (motive : Expr → Expr → Sort u_1)
  (h_1 :
    Unit →
      motive (((sort zero.succ).app (sort zero.succ)).app (sort zero.succ))
        (((sort zero.succ).app (sort zero.succ)).app (sort zero.succ)))
  (h_2 : (x x_1 : Expr) → motive x x_1) :
  (match ((sort zero.succ).app (sort zero.succ)).app (sort zero.succ),
      ((sort zero.succ).app (sort zero.succ)).app (sort zero.succ) with
    | ((sort zero.succ).app (sort zero.succ)).app (sort zero.succ),
      ((sort zero.succ).app (sort zero.succ)).app (sort zero.succ) => h_1 ()
    | x, x_1 => h_2 x x_1) =
    h_1 ()
-/
#guard_msgs in
#check expensive.match_1.eq_1
/--
info: expensive.match_1.eq_2.{u_1} (motive : Expr → Expr → Sort u_1) (x✝ x✝¹ : Expr)
  (h_1 :
    Unit →
      motive (((sort zero.succ).app (sort zero.succ)).app (sort zero.succ))
        (((sort zero.succ).app (sort zero.succ)).app (sort zero.succ)))
  (h_2 : (x x_1 : Expr) → motive x x_1) :
  (x✝ = ((sort zero.succ).app (sort zero.succ)).app (sort zero.succ) →
      x✝¹ = ((sort zero.succ).app (sort zero.succ)).app (sort zero.succ) → False) →
    (match x✝, x✝¹ with
      | ((sort zero.succ).app (sort zero.succ)).app (sort zero.succ),
        ((sort zero.succ).app (sort zero.succ)).app (sort zero.succ) => h_1 ()
      | x, x_1 => h_2 x x_1) =
      h_2 x✝ x✝¹
-/
#guard_msgs in
#check expensive.match_1.eq_2

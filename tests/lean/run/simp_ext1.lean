import data.list
open list tactic option
constants (A : Type.{1}) (x y z : A) (Hy : x = y) (Hz : y = z)

meta_definition simp_x_to_y : tactic unit :=
do gs ← get_goals,
   match gs with
   | [g] := do tgt ← target,
               match expr.is_eq tgt with
               | none := fail "simplifier extension expects a goal of the form [ctx |- l = ?r]"
               | some (start, res) := do mk_const "y" >>= unify res,
                                         mk_const "Hy" >>= unify g
               end
   | _ := fail "simplifier extension expects a goal of the form [ctx |- l = ?r]"
   end

meta_definition simp_y_to_z : tactic unit :=
do gs ← get_goals,
   match gs with
   | [g] := do tgt ← target,
               match expr.is_eq tgt with
               | none := fail "simplifier extension expects a goal of the form [ctx |- l = ?r]"
               | some (start, res) := do mk_const "z" >>= unify res,
                                         mk_const "Hz" >>= unify g
               end
   | _ := fail "simplifier extension expects a goal of the form [ctx |- l = ?r]"
   end

register_simp_ext x simp_x_to_y
register_simp_ext y simp_y_to_z

print [simp_ext]
example : x = z := by simp >> triv

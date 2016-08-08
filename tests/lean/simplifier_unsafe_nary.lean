open tactic

universe l
constants (A : Type.{l}) (op : A → A → A → A)
          (op_assoc : Π a, is_associative (op a))
          (a b x y z : A)

attribute op_assoc [instance]

print "Safe version, should not simplify"
set_option simplify.unsafe_nary false
example : (op a) ((op b) x y) z = (op a) x ((op b) y z) := by simp

print "Unsafe version, should simplify and the proof should be incorrect"

set_option simplify.unsafe_nary true
example : (op a) ((op b) x y) z = (op a) x ((op b) y z) := by simp

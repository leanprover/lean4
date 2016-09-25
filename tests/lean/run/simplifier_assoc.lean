open tactic
constants (A : Type 1) (a b c d e f g h : A) (op : A → A → A) (op_assoc : is_associative op)
attribute [instance] op_assoc

infixr `%%` := op

namespace pat2
constant H : a %% b = f
local attribute [simp] H

example : a %% b = f := by simp
example : c %% a %% b = c %% f := by simp
example : a %% b %% c = f %% c := by simp
example : c %% a %% b %% d = c %% f %% d := by simp
example : c %% d %% a %% b %% c %% d = c %% d %% f %% c %% d := by simp

end pat2

namespace pat3
constant H : (a %% b) %% g = f
attribute [simp] H

example : a %% b %% g = f := by simp
example : c %% a %% b %% g = c %% f := by simp
example : a %% b %% g %% c = f %% c := by simp
example : c %% a %% b %% g %% d = c %% f %% d := by simp
example : c %% d %% a %% b %% g %% c %% d = c %% d %% f %% c %% d := by simp

end pat3

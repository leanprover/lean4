open tactic

universe l
constants (A : Type.{l}) (f g : A → A) (op : A → A → A) (x y z w b c : A)
infixr `%%` := op

namespace basic
constants (Hf : f x = y)
constants (Hff : f (f x) = z)

attribute [simp] Hff Hf

set_option simplify.topdown true
example : f (f x) = z := by simp

set_option simplify.topdown false
example : f (f x) = f y := by simp

end basic

namespace iterated
constants (Hf : f x = y)
constants (Hff : f (f x) = z)
constants (Hw : w = f (f x))

attribute [simp] Hff Hf Hw

set_option simplify.topdown true
example : w = z := by simp

set_option simplify.topdown false
example : w = f y := by simp

attribute [reducible] noncomputable definition u := f (f x)

set_option simplify.topdown true
example : u = z := by simp

set_option simplify.topdown false
example : u = f y := by simp

end iterated

namespace nary
constants (assoc : is_associative op)
attribute [instance] assoc

constants (Hf : f x = y)
constants (Hff : f (f x) = z)

constants (Hof : x %% (f y) = b)
constants (Hoff : x %% f (f x) = c)
attribute [simp] Hf Hff Hof Hoff

set_option simplify.topdown true
example : x %% f (f x) %% x %% f (f x) = c %% c := by simp

set_option simplify.topdown false
example : x %% f (f x) %% x %% f (f x) = b %% b := by simp

end nary

namespace nary_iterated
constants (assoc : is_associative op)
attribute [instance] assoc

constants (Hf : f x = y)
constants (Hff : f (f x) = z)

constants (Hof : x %% (f y) = b)
constants (Hoff : x %% f (f x) = c)

constants (Hw : w = f (f x))

attribute [simp] Hf Hff Hof Hoff Hw

set_option simplify.topdown true
example : x %% w %% x %% w = x %% z %% x %% z := by simp

set_option simplify.topdown false
example : x %% w %% x %% w = b %% b := by simp

end nary_iterated

open tactic

constant f : nat → nat

meta def check_expr (p : pexpr) (t : expr) : tactic unit :=
do e ← to_expr p, guard (t = e)

namespace foo
axiom f_lemma1 : f 0 = 1
namespace bla
axiom f_lemma2 : f 1 = 2

def g (a : nat) := a + 1

example : g 0 = 1 :=
begin
  unfold g
end

example : f (f 0) = 2 :=
by rewrite [f_lemma1, f_lemma2]

lemma ex2 : f (f 0) = 2 :=
by simp [f_lemma1, f_lemma2]

end bla
end foo

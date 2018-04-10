universe variables u v

structure Func :=
(A : Type u) (B : A → Type v) (fn : Π a, B a → B a)

instance F_to_fn : has_coe_to_fun Func :=
{ F   := λ f, Π a, f^.B a → f^.B a,
  coe := λ f a b, f^.fn a (f^.fn a b) }

variables (f : Func) (a : f^.A) (b : f^.B a)
#check (f a b)

def f1 : Func :=
{ A  := nat,
  B  := λ a, nat,
  fn := (+) }

-- set_option trace.type_context.is_def_eq_detail true

/- We need to mark 10 as a nat.
   Reason: f1 is not reducible, then type class resolution
   cannot find an instance for `has_one (Func.A f1)` -/
example : f1 (10:nat) (30:nat) = (50:nat) :=
rfl

/-
#exit

attribute [reducible] f1

example : f1 10 30 = 50 :=
rfl

example (n m : nat) : f1 n m = n + (n + m) :=
rfl
-/

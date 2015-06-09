open nat

inductive type : Type :=
| Nat  : type
| Func : type → type → type

open type

section var
variable {var : type → Type}

inductive term : type → Type :=
| Var   : ∀ {t}, var t → term t
| Const : nat → term Nat
| Plus  : term Nat → term Nat → term Nat
| Abs   : ∀ {dom ran}, (var dom → term ran) → term (Func dom ran)
| App   : ∀ {dom ran}, term (Func dom ran) → term dom → term ran
| Let   : ∀ {t1 t2}, term t1 → (var t1 → term t2) → term t2
end var

open term

definition Term t := Π (var : type → Type), @term var t
open unit

-- Define count_vars using tactics
definition count_vars1 {t : type} (T : @term (λ x, unit) t) : nat :=
begin
  induction T,
    {exact 1},
    {exact 0},
    {exact v_0 + v_1},
    {exact v_0 star},
    {exact v_0 + v_1},
    {exact v_0 + v_1 star},
end

-- Define count_vars using recursor
definition count_vars2 {t : type} (T : @term (λ x, unit) t) : nat :=
term.rec_on T
  (λ t u, 1)
  (λ n, 0)
  (λ T₁ T₂ n₁ n₂, n₁ + n₂)
  (λ d r f n, n star)
  (λ d r T₁ T₂ n₁ n₂, n₁ + n₂)
  (λ t₁ t₂ T₁ T₂ n₁ n₂, n₁ + n₂ star)

definition var (t : type) : @term (λ x, unit) t :=
Var star

example : count_vars1 (App (App (var (Func Nat (Func Nat Nat))) (var Nat)) (var Nat)) = 3 :=
rfl

example : count_vars2 (App (App (var (Func Nat (Func Nat Nat))) (var Nat)) (var Nat)) = 3 :=
rfl

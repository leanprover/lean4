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

definition count_vars : Π {t : type}, @term (λ x, unit) t -> nat
| count_vars (Var _)       := 1
| count_vars (Const _)     := 0
| count_vars (Plus e1 e2)  := count_vars e1 + count_vars e2
| count_vars (Abs e1)      := count_vars (e1 star)
| count_vars (App e1 e2)   := count_vars e1 + count_vars e2
| count_vars (Let e1 e2)   := count_vars e1 + count_vars (e2 star)

definition var (t : type) : @term (λ x, unit) t :=
Var star

example : count_vars (App (App (var (Func Nat (Func Nat Nat))) (var Nat)) (var Nat)) = 3 :=
rfl

definition count_vars2 : Π {t : type}, @term (λ x, unit) t -> nat
| _  (Var _)       := 1
| _  (Const _)     := 0
| _  (Plus e1 e2)  := count_vars2 e1 + count_vars2 e2
| _  (Abs e1)      := count_vars2 (e1 star)
| _  (App e1 e2)   := count_vars2 e1 + count_vars2 e2
| _  (Let e1 e2)   := count_vars2 e1 + count_vars2 (e2 star)

open nat

inductive type : Type
| Nat  : type
| Func : type → type → type

open type

section var
variable {var : type → Type}

inductive term : type → Type
| Var   : ∀ {t}, var t → term t
| Const : nat → term Nat
| Plus  : term Nat → term Nat → term Nat
| Abs   : ∀ {dom ran}, (var dom → term ran) → term (Func dom ran)
| App   : ∀ {dom ran}, term (Func dom ran) → term dom → term ran
| Let   : ∀ {t1 t2}, term t1 → (var t1 → term t2) → term t2
end var

open term

definition Term (t) := Π (var : type → Type), @term var t
open unit

definition count_vars : Π {t : type}, @term (λ x, unit) t -> nat
| A          (Var x)                := 1
| Nat        (Const x)              := 0
| Nat        (Plus e1 e2)           := count_vars e1 + count_vars e2
| (Func A B) (Abs e1)               := count_vars (e1 star)
| B          (@App ._ A .(B) e1 e2)   := count_vars e1 + count_vars e2
| B          (@Let ._ A .(B) e1 e2)   := count_vars e1 + count_vars (e2 star)

definition var (t : type) : @term (λ x, unit) t :=
Var star

example : count_vars (App (App (var (Func Nat (Func Nat Nat))) (var Nat)) (var Nat)) = 3 :=
rfl

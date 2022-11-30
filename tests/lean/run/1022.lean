namespace STLC

abbrev Var := Char

inductive Ty where
  | base  : Ty
  | arrow : Ty → Ty → Ty

inductive Term where
  | var : Var → Term
  | lam : Var → Ty → Term → Term
  | app : Term → Term → Term

def ctx := List (Var × Ty)

open Ty Term in
inductive Typing : ctx → Term → Ty → Prop where
  | var  : Typing ((x, A) :: Γ) (var x) A -- simplified
  | arri : Typing ((x, A) :: Γ) M B → Typing Γ (lam x A M) (arrow A B)
  | arre : Typing Γ M (arrow A B) → Typing Γ N A → Typing Γ (app M N) B

open Ty Term in
theorem no_δ : ¬ ∃ A B, Typing nil (lam x A (app (var x) (var x))) (arrow A B) :=
  fun h => match h with
  | Exists.intro A (Exists.intro B h) => match h with
    | Typing.arri h => match h with
      | Typing.arre (A := T) h₁ h₂ => match h₂ with
        | Typing.var => nomatch h₁

namespace STLC

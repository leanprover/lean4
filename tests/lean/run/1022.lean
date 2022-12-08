namespace STLC

abbrev Var := Char

inductive type where
  | base  : type
  | arrow : type → type → type

inductive term where
  | var : Var → term
  | lam : Var → type → term → term
  | app : term → term → term

def ctx := List (Var × type)

open type term in
inductive typing : ctx → term → type → Prop where
  | var  : typing ((x, A) :: Γ) (var x) A -- simplified
  | arri : typing ((x, A) :: Γ) M B → typing Γ (lam x A M) (arrow A B)
  | arre : typing Γ M (arrow A B) → typing Γ N A → typing Γ (app M N) B

open type term in
theorem no_δ : ¬ ∃ A B, typing nil (lam x A (app (var x) (var x))) (arrow A B) :=
  fun h => match h with
  | Exists.intro A (Exists.intro B h) => match h with
    | typing.arri h => match h with
      | typing.arre (A := T) h₁ h₂ => match h₂ with
        | typing.var => nomatch h₁

namespace STLC

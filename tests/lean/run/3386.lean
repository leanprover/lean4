/- Verify that injectivity lemmas are constructed with the right level of generality
   in order to avoid type errors.
-/

inductive Tyₛ : Type (u+1)
| SPi : (T : Type u) -> (T -> Tyₛ) -> Tyₛ

inductive Tmₛ.{u} :  Tyₛ.{u} -> Type (u+1)
| app : Tmₛ (.SPi T A) -> (arg : T) -> Tmₛ (A arg)

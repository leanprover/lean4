/- Verify that injectivity lemmas are constructed with the right level of generality
   in order to avoid type errors.
-/

inductive Tyₛ : Type (u+1)
| SPi : (T : Type u) -> (T -> Tyₛ) -> Tyₛ

set_option deriving.decEq.linear_construction_threshold 0
inductive Tmₛ.{u} :  Tyₛ.{u} -> Type (u+1)
| app : Tmₛ (.SPi T A) -> (arg : T) -> Tmₛ (A arg)

/--
info: Tmₛ.app.injEq.{u} {T : Type u} {A : T → Tyₛ} (a✝ : Tmₛ (Tyₛ.SPi T A)) (arg : T) (a✝¹ : Tmₛ (Tyₛ.SPi T A)) :
  (a✝.app arg = a✝¹.app arg) = (a✝ = a✝¹)
-/
#guard_msgs in
#check Tmₛ.app.injEq

/--
info: Tmₛ.app.inj.{u} {T : Type u} {A : T → Tyₛ} {a✝ : Tmₛ (Tyₛ.SPi T A)} {arg : T} {a✝¹ : Tmₛ (Tyₛ.SPi T A)} :
  a✝.app arg = a✝¹.app arg → a✝ = a✝¹
-/
#guard_msgs in
#check Tmₛ.app.inj

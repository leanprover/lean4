inductive test0 : Type → Type
| intro : (λ t, t → test0 t) nat

inductive test1 : Type → Type
| intro : let t := nat in t → test1 t

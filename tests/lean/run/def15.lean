

def head {α} : (as : List α) → as ≠ [] → α
| [],    h => absurd rfl h
| a::as, _ => a

theorem head_cons {α} (a : α) (as : List α) : head (a::as) (fun h => List.noConfusion h) = a :=
rfl

theorem head_cons' {α} (a : α) (as : List α) (h : a::as ≠ []) : head (a::as) h = a :=
rfl

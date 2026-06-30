
universe u

def len {α : Type u} : List α → List α → Nat
| [],    bs => bs.length
| a::as, bs => len as bs + 1

theorem ex1 : len [1, 2] [3, 4] = 4 :=
rfl

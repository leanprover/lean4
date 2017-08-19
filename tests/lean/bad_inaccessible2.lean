universe variables u
inductive vec (A : Type u) : nat → Type (max 1 u)
| nil {} : vec 0
| cons   : Π {n}, A → vec n → vec (n+1)

open vec

variables {A : Type u}
variables f : A → A → A

/- The new equation compiler can process this example.
   So, this is not a test about error messages anymore.
-/
def map_head : ∀ {n}, vec A n → vec A n → vec A n
| .(0)     nil nil                       := nil
| .(n+1) (@cons .(A) .(n) a va) (@cons .(A) n b vb) := cons (f a b) va

/- The following shorter version is also accepted. -/
def map_head2 : ∀ {n}, vec A n → vec A n → vec A n
| _ nil         nil         := nil
| _ (cons a va) (cons b vb) := cons (f a b) va

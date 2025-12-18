/- Dependent pattern matching -/

inductive Vector (α : Type u) : Nat → Type u
  | nil : Vector α 0
  | cons : α → Vector α n → Vector α (n+1)

infix:67 "::" => Vector.cons

def Vector.zip : Vector α n → Vector β n → Vector (α × β) n
  | nil, nil => nil
  | a::as, b::bs => (a, b) :: zip as bs

#print Vector.zip
/-
def Vector.zip.{u_1, u_2} : {α : Type u_1} → {n : Nat} → {β : Type u_2} → Vector α n → Vector β n → Vector (α × β) n :=
fun {α} {n} {β} x x_1 =>
  Vector.brecOn (motive := fun {n} x => {β : Type u_2} → Vector β n → Vector (α × β) n) x
    ...
-/

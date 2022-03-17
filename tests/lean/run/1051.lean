inductive SF : Type u → Type u → Type (u+1) where
|  seq {as bs cs: Type u}: SF as bs → SF bs cs → SF as cs
|  fan {as bs cs: Type u}: SF as (bs × cs)

inductive SF' (m: Type (u+1) → Type u)[Monad m]: Type u → Type u → Type (u+1) where
|  seq       {as bs cs: Type u}: SF' m as bs → SF' m bs cs → SF' m as cs
|  fan       {as bs cs: Type u}: SF' m as (bs × cs)
|  rswitcher {as bs cs: Type u}: SF' m as (bs × cs) → SF' m as bs

def SF.step [Monad m] (sa: as): SF as bs → SF' m as bs × bs
| seq sf₁ sf₂ =>
  let (sf₁', sb) := sf₁.step sa
  let (sf₂', sc) := sf₂.step sb
  (sf₁'.seq sf₂', sc)
| fan => sorry

def SF'.step [Monad m] (sa: as): SF' m as bs → SF'.{u} m as bs × bs
| seq sf₁ sf₂ =>
  let (sf₁', sb) := sf₁.step sa
  let (sf₂', sc) := sf₂.step sb
  (sf₁'.seq sf₂', sc)
| fan => sorry
| rswitcher f =>
  let x := f.step sa
  let (_, (sb, _)) := x
  (rswitcher f, sb)

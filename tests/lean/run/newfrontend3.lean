structure S  :=
(g {α} : α → α)

def f (h : Nat → (forall {α : Type}, α → α) × Bool) : Nat :=
(h 0).1 1

new_frontend

def tst : Nat :=
f (fun n => (fun x => x, true))

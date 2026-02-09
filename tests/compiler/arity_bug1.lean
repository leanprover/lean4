/-!
This is a regression test reproducer for #10925
-/

inductive Countdown where
  | zero
  | one

def MyStateT (σ : Type u) (m : Type u → Type v) (α : Type u) : Type (max u v) :=
  σ → m (α × σ)

def MyStateT.run {σ : Type u} {m : Type u → Type v} {α : Type u} (x : MyStateT σ m α) (s : σ) : m (α × σ) :=
  x s

namespace MyStateT
variable {σ : Type u} {m : Type u → Type v}
variable [Monad m] {α β : Type u}

protected def pure (a : α) : MyStateT σ m α :=
  fun s => pure (a, s)

protected def bind (x : MyStateT σ m α) (f : α → MyStateT σ m β) : MyStateT σ m β :=
  fun s => do let (a, s) ← x s; f a s

instance : Monad (MyStateT σ m) where
  pure := MyStateT.pure
  bind := MyStateT.bind

end MyStateT

partial def Countdown.forM [Monad m] (c : Countdown) : m PUnit :=
  match c with
  | zero => pure ()
  | one =>
    (·.1) <$> (MyStateT.run (Countdown.forM (m := MyStateT Unit m) Countdown.zero) ())

def main : IO Unit := do
  Countdown.one.forM
  IO.println "ok"

def f (v : Nat) : StateRefT Nat IO Nat := do
IO.println "hello";
modify fun s => s - v;
get

def g : IO Nat :=
(f 5).run' 20

#eval (f 5).run' 20

#eval (do set 100; f 5).run' 0

def f2 : ReaderT Nat (StateRefT Nat IO) Nat := do
v ← read;
IO.println $ "context " ++ toString v;
modify fun s => s + v;
get

#eval (f2.run 10).run' 20

def f3 : StateT String (StateRefT Nat IO) Nat := do
s ← get;
n ← getThe Nat;
set (s ++ ", " ++ toString n);
s ← get;
IO.println s;
set (n+1);
getThe Nat

#eval (f3.run' "test").run' 10

structure Label {β : Type} (v : β) (α : Type) :=
(val : α)

class HasGetAt {β : Type} (v : β) (α : outParam Type) (m : Type → Type) :=
(getAt : m α)

instance monadState.hasGetAt (β : Type) (v : β) (α : Type) (m : Type → Type) [Monad m] [MonadStateOf (Label v α) m] : HasGetAt v α m :=
{ getAt := do a ← getThe (Label v α); pure a.val }

export HasGetAt (getAt)

abbrev M := StateRefT (Label 0 Nat) $ StateRefT (Label 1 Nat) $ StateRefT (Label 2 Nat) IO

def f4 : M Nat := do
a0 : Nat ← getAt 0;
a1 ← getAt 1;
a2 ← getAt 2;
IO.println $ "state0 " ++ toString a0;
IO.println $ "state1 " ++ toString a1;
IO.println $ "state1 " ++ toString a2;
pure (a0 + a1 + a2)

#eval ((f4.run' ⟨10⟩).run' ⟨20⟩).run' ⟨30⟩

abbrev N := StateRefT Nat $ ExceptT Bool $ StateRefT Bool $ IO

def f5 : N Nat := do
a : Nat ← get;
b ← getThe Bool;
pure a

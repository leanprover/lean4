def loop (x : Nat) : Unit := loop (x + 1)
termination_by tailrecursion

/--
info: equations:
theorem loop.eq_1 : ∀ (x : Nat), loop x = loop (x + 1)
-/
#guard_msgs in
#print equations loop

/-- error: unknown constant 'loop.induct' -/
#guard_msgs in
#check loop.induct

def find (P : Nat → Bool) (x : Nat) : Option Nat :=
  if P x then
    some x
  else
    find P (x +1)
termination_by tailrecursion

/--
info: equations:
theorem find.eq_1 : ∀ (P : Nat → Bool) (x : Nat), find P x = if P x = true then some x else find P (x + 1)
-/
#guard_msgs in
#print equations find

/--
error: Termination by tailrecursion needs a nonempty codomain:
  failed to synthesize
    Nat → Nonempty (Fin n)
  Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
def notinhabited (n m : Nat) : Fin n :=
  notinhabited n (m+1)
termination_by tailrecursion

def fib (n : Nat) := go 0 0 1
where
  go i fip fi :=
    if i = n then
      fi
    else
      go (i + 1) fi (fi + fip)
  termination_by tailrecursion

local instance (b : Bool) [Nonempty α] [Nonempty β] : Nonempty (if b then α else β) := by
  split <;> assumption

def dependent1 (b : Bool) (n : Nat) : if b then Nat else Bool
  := dependent1 b (n + 1)
termination_by tailrecursion

def dependent2 (b : Bool) (n : Nat) : if b then Nat else Bool :=
  if b then dependent2 b (n + 1) else dependent2 b (n +1)
termination_by tailrecursion

/--
error: Could not prove function to be tailrecursive:
  Recursive call in non-tail position:
    if b = true then f ⟨a + 1, b⟩ else f ⟨a + 1, b⟩
-/
#guard_msgs in
def dependent2' (n : Nat) (b : Bool) : if b then Nat else Bool :=
  if b then dependent2' (n + 1) b else dependent2' (n +1) b
termination_by tailrecursion

local instance (b : Bool) [Nonempty α] [Nonempty β] : Nonempty (cond b α β) := by
  cases b <;> assumption

/--
error: Could not prove function to be tailrecursive:
  Recursive call in non-tail position:
    match a with
    | true => f ⟨true, b + 1⟩
    | false => f ⟨false, b + 1⟩
-/
#guard_msgs in
def dependent3 (b : Bool) (n : Nat) : cond b Nat Bool :=
  match b with
  | true => dependent3 true (n + 1)
  | false => dependent3 false (n +1)
termination_by tailrecursion

example
  (a : Bool)
  (b : Nat) :
  Lean.Tailrec.mono fun (f : (x : (_ : Bool) ×' Nat) → cond x.1 Nat Bool) =>
    match (motive := ∀ a, cond a Nat Bool) a with
    | true => f ⟨true, b + 1⟩
    | false => f ⟨false, b + 1⟩ := by
  split
  · apply Lean.Tailrec.mono_apply
  · apply Lean.Tailrec.mono_apply

local instance {α : Sort u} {β : Sort v} {γ : α → Sort uu} {δ : β → Sort uu} (t : α ⊕' β)
  [inst1 : ∀ x, Nonempty (γ x)] [inst2 : ∀ x, Nonempty (δ x)] : Nonempty (t.casesOn γ δ) := by
  cases t
  · apply inst1
  · apply inst2

#guard_msgs in
mutual
def mutual1 (n m : Nat) : Unit := mutual2 (m + 1) n
termination_by tailrecursion
def mutual2 (n m : Nat) : Unit := mutual1 (m + 1) n
termination_by tailrecursion
end

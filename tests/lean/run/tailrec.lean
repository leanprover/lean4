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
error: failed to compile definition 'notinhabited' via tailrecursion, could not prove that the type
  (n : Nat) → Nat → Fin n
is nonempty.

This process uses multiple strategies:
- It looks for a parameter that matches the return type.
- It tries synthesizing 'Inhabited' and 'Nonempty' instances for the return type, while making every parameter into a local 'Inhabited' instance.
- It tries unfolding the return type.

If the return type is defined using the 'structure' or 'inductive' command, you can try adding a 'deriving Nonempty' clause to it.
-/
#guard_msgs in
def notinhabited (n m : Nat) : Fin n :=
  notinhabited n (m+1)
termination_by tailrecursion

/--
error: failed to compile definition 'notinhabited_mutual1' via tailrecursion, could not prove that the type
  (n : Nat) → Nat → Fin n
is nonempty.

This process uses multiple strategies:
- It looks for a parameter that matches the return type.
- It tries synthesizing 'Inhabited' and 'Nonempty' instances for the return type, while making every parameter into a local 'Inhabited' instance.
- It tries unfolding the return type.

If the return type is defined using the 'structure' or 'inductive' command, you can try adding a 'deriving Nonempty' clause to it.
-/
#guard_msgs in
mutual
def notinhabited_mutual1 (n m : Nat) : Fin n :=
  notinhabited_mutual2 n (m+1)
termination_by tailrecursion
def notinhabited_mutual2 (n m : Nat) : Fin n :=
  notinhabited_mutual1 n (m+1)
termination_by tailrecursion
end


/--
error: Could not prove function to be tailrecursive:
  Recursive call in non-tail position:
    f (x + 1) - 1
-/
#guard_msgs in
def notTailRec1 (n : Nat) := notTailRec1 (n + 1) - 1
termination_by tailrecursion

/--
error: Could not prove function to be tailrecursive:
  Recursive call in non-tail position:
    f (x + 1) - 1
-/
#guard_msgs in
def notTailRec2 (n m : Nat) := notTailRec2 n (m + 1) - 1
termination_by tailrecursion

/--
error: Could not prove function to be tailrecursive:
  Recursive call in non-tail position:
    f ⟨b + 1, a⟩ - 1
-/
#guard_msgs in
def notTailRec3 (n m : Nat) := notTailRec3 (m + 1) n - 1
termination_by tailrecursion

/--
error: Could not prove function to be tailrecursive:
  Recursive call in non-tail position:
    f (PSum.inr ⟨b + 1, a⟩) - 1
-/
#guard_msgs in
mutual
def notTailRec4a (n m : Nat) := notTailRec4b (m + 1) n - 1
termination_by tailrecursion
def notTailRec4b (n m : Nat) := notTailRec4a (m + 1) n - 1
termination_by tailrecursion
end

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
  if b then dependent2 b (n + 1) else dependent2 b (n + 1)
termination_by tailrecursion

def dependent2' (n : Nat) (b : Bool) : if b then Nat else Bool :=
  if b then dependent2' (n + 1) b else dependent2' (n + 2) b
termination_by tailrecursion

def dependent2'' (n : Nat) (b : Bool) : if b then Nat else Bool :=
  if _ : b then dependent2'' (n + 1) b else dependent2'' (n + 2) b
termination_by tailrecursion

local instance (b : Bool) [Nonempty α] [Nonempty β] : Nonempty (cond b α β) := by
  cases b <;> assumption

def dependent3 (b : Bool) (n : Nat) : cond b Nat Bool :=
  match b with
  | true => dependent3 true (n + 1)
  | false => dependent3 false (n + 2)
termination_by tailrecursion


local instance {α : Sort u} {β : Sort v} {γ : α → Sort uu} {δ : β → Sort uu} (t : α ⊕' β)
  [inst1 : ∀ x, Nonempty (γ x)] [inst2 : ∀ x, Nonempty (δ x)] : Nonempty (t.casesOn γ δ) := by
  cases t
  · apply inst1
  · apply inst2

mutual
def mutual1 (n m : Nat) : Unit := mutual2 (m + 1) n
termination_by tailrecursion
def mutual2 (n m : Nat) : Unit := mutual1 (m + 1) n
termination_by tailrecursion
end

def computeLfp' {α : Type u} [DecidableEq α] (f : α → α) (x : α) : α :=
  let next := f x
  if x ≠ next then
    computeLfp' f next
  else
    x
termination_by tailrecursion

def whileSome (f : α → Option α) (x : α) : α :=
  match f x with
  | none => x
  | some x' => whileSome f x'

/--
info: whileSome.eq_1.{u_1} {α : Type u_1} (f : α → Option α) (x : α) :
  whileSome f x =
    match f x with
    | none => x
    | some x' => whileSome f x'
-/
#guard_msgs in #check whileSome.eq_1

/-!
# Tests of cdot functions
-/

set_option pp.mvars false

class Inc (α : Type) :=
(inc : α → α)

export Inc (inc)

instance {α} [Inc α] : Inc (List α) :=
{ inc := (·.map inc) }

instance : Inc Nat :=
{ inc := Nat.succ }

#guard inc 10 == 11
#guard inc [1, 2, 3] == [2, 3, 4]

theorem ex1 : [(1, "hello"), (2, "world")].map (·.1) = [1, 2] :=
rfl

theorem ex2 : [(1, "hello"), (2, "world")].map (·.snd) = ["hello", "world"] :=
rfl

def sum (xs : List Nat) : Nat :=
(·.2) $ Id.run $ StateT.run (s:=0) do
  xs.forM fun x => modify (· + x)

#guard sum [1, 2, 3, 4] == 10

theorem ex3 : sum [1, 2, 3] = 6 :=
rfl

theorem ex4 : sum [1, 2, 3, 4] = 10 :=
rfl

/-!
Check that ambiguous notation inside cdot notation still has only a single argument.
(Need to process choice nodes specially.)
-/

def tag (_ : α) (y : α) := y
notation "f" x => tag 1 x
notation "f" x => tag "2" x
/-- info: fun x => (f x).length : String → Nat -/
#guard_msgs in
#check (String.length <| f ·)

/-!
Check that cdots can't be captured in `let` functions
(there is a type ascription the body syntax is inserted into).
-/
/--
error: invalid occurrence of `·` notation, it must be surrounded by parentheses (e.g. `(· + 1)`)
---
error: invalid occurrence of `·` notation, it must be surrounded by parentheses (e.g. `(· + 1)`)
-/
#guard_msgs in
def a : Nat → Nat → Nat :=
  let (add) : Nat → Nat → Nat := · + ·
  add

/-!
Check that cdots can't be captured in macros.
-/
macro "baz% " t:term : term => `(1 + ($t))
/--
error: invalid occurrence of `·` notation, it must be surrounded by parentheses (e.g. `(· + 1)`)
---
info: 1 + sorry : Nat
-/
#guard_msgs in #check baz% ·
/-!
Note that cdots still work here since they are expanded before the inner macro is expanded.
-/
/-- info: fun x => 1 + x : Nat → Nat -/
#guard_msgs in #check (baz% ·)

/-!
Check that parentheses, type ascriptions, and tuples each delimit cdot expansion.
-/
/-- info: fun x => x ∘ fun x => x : (?_ → ?_) → ?_ → ?_ -/
#guard_msgs in #check (· ∘ (·))
/-- info: fun x => x ∘ fun x => x : (Nat → ?_) → Nat → ?_ -/
#guard_msgs in #check (· ∘ (· : Nat → Nat))
/-- info: fun x => (x, fun x_1 => (1, x_1)) : (x : ?_) → ?_ × (?_ x → Nat × ?_ x) -/
#guard_msgs in #check (·, (1, ·))

/-!
Function extensionality split candidates are indexed by the parent function and argument
position. A lambda that occurs as an argument of two different applications (or at two positions
of the same application) must be recorded under each of them. Before the fix, only the first
occurrence was recorded, so the candidate `(fun x => k x a) = (fun x => k x b)` below was never
created when the first occurrence of the lambda was under a different parent.
-/

-- The lambda `fun x => k x a` occurs first under `g`, then under `f`.
example (k : Nat → Nat → Nat) (f : (Nat → Nat) → Nat) (g : (Nat → Nat) → Prop) (a b : Nat)
    (_ : g (fun x => k x a)) (h : a = b) : f (fun x => k x a) = f (fun x => k x b) := by
  grind

-- The lambda `fun x => k x b` occurs first under `g`, then under `f`.
example (k : Nat → Nat → Nat) (f : (Nat → Nat) → Nat) (g : (Nat → Nat) → Prop) (a b : Nat)
    (_ : g (fun x => k x b)) (h : a = b) : f (fun x => k x a) = f (fun x => k x b) := by
  grind

-- The lambda `fun x => k x b` occurs at two argument positions of `f`.
example (k : Nat → Nat → Nat) (f : (Nat → Nat) → (Nat → Nat) → Nat) (a b : Nat)
    (h : a = b) : f (fun x => k x b) (fun x => k x a) = f (fun x => k x b) (fun x => k x b) := by
  grind

-- The lambda occurs in a hypothesis under `g` and in the goal under `f`, with `g` applied twice.
example (k : Nat → Nat → Nat) (f : (Nat → Nat) → Nat) (g : (Nat → Nat) → Prop) (a b : Nat)
    (_ : g (fun x => k x a)) (_ : g (fun x => k x b)) (h : a = b) :
    f (fun x => k x a) = f (fun x => k x b) := by
  grind

-- Both occurrences are under the same application.
example (k : Nat → Nat → Nat) (f : (Nat → Nat) → (Nat → Nat) → Nat) (a b : Nat)
    (h : a = b) : f (fun x => k x a) (fun x => k x a) = f (fun x => k x b) (fun x => k x b) := by
  grind

-- No hypothesis needed: the lambdas are already equal up to `a = b`.
example (k : Nat → Nat → Nat) (f : (Nat → Nat) → Nat) (a b : Nat)
    (h : a = b) : f (fun x => k x a) = f (fun x => k x b) := by
  grind

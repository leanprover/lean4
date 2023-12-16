/-!
If the recursive call is passed to the `case` tactic, it
gets duplicate fairly often, and into different contexts
(see below)
So let us construct proofs that depend on that context,
to check that the proofs are not confused.

A work-around is
```
  let r := foo n
  cases r
```
-/

-- set_option trace.Elab.definition.wf true
def foo : (n : Nat) → ∃ m, m > n
 | 0 => ⟨1, Nat.zero_lt_one⟩
 | n+1 => by
  cases foo n
  · case _ m hm => exact ⟨m+1, Nat.succ_lt_succ hm⟩
decreasing_by

  -- trace_state
  solve
  | have this_is_in_the_context : ∃ m, m > n := by assumption
    cases this_is_in_the_context
    exact Nat.lt_succ_self _
  | exact Nat.lt_succ_self _


/-
[Elab.definition.wf] replaceRecApps:
      match n with
      | 0 => Exists.intro 1 Nat.zero_lt_one
      | Nat.succ n =>
        Exists.casesOn (motive := fun t => foo n = t → ∃ m, m > n + 1) (foo n)
          (fun w h h_1 => Exists.intro (w + 1) (Nat.succ_lt_succ h)) (Eq.refl (foo n))
-/

/-

Contexts

n: Nat
x✝: ∀ (y : Nat), (invImage (fun a => sizeOf a) instWellFoundedRelation).1 y (Nat.succ n) → ∃ m, m > y
t✝: ∃ m, m > n
⊢ (invImage (fun a => sizeOf a) instWellFoundedRelation).1 n (Nat.succ n)
n: Nat
x✝: ∀ (y : Nat), (invImage (fun a => sizeOf a) instWellFoundedRelation).1 y (Nat.succ n) → ∃ m, m > y
⊢ (invImage (fun a => sizeOf a) instWellFoundedRelation).1 n (Nat.succ n)
n: Nat
x✝: ∀ (y : Nat), (invImage (fun a => sizeOf a) instWellFoundedRelation).1 y (Nat.succ n) → ∃ m, m > y
w✝: Nat
h✝: w✝ > n
⊢ (invImage (fun a => sizeOf a) instWellFoundedRelation).1 n (Nat.succ n)
n: Nat
x✝: ∀ (y : Nat), (invImage (fun a => sizeOf a) instWellFoundedRelation).1 y (Nat.succ n) → ∃ m, m > y
⊢ (invImage (fun a => sizeOf a) instWellFoundedRelation).1 n (Nat.succ n)
-/

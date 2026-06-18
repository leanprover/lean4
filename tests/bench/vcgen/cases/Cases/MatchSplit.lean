import Lean
import Std.Tactic.Do

/-!
Pattern matching where the discriminant *is* the symbolic state (`match s with ...` after
`let s ← get`). Unlike `MatchIota`, the discriminant is not a literal, so VC generation must
perform a genuine match split. The initial state is kept symbolic (via `s = n`) so the split
is not iota-reduced away. Starting at `s = n`, each `step` decrements the state by one, ending
at `0` after exactly `n` steps without ever throwing.
-/

open Lean Meta Order Std.Internal.Do

namespace MatchSplit

set_option mvcgen.warning false

abbrev M := ExceptT String <| StateM Nat

@[spec high] theorem spec_throw (e : String) {post : α → Nat → Prop} :
    ⦃epost e⦄ (throw (m := M) e) ⦃post; epost⟨epost⟩⦄ := ⟨PartialOrder.rel_refl⟩

@[spec high] theorem spec_set (x : Nat) {post : PUnit → Nat → Prop} :
    ⦃fun _ => post ⟨⟩ x⦄ (set (m := M) x) ⦃post⦄ := ⟨PartialOrder.rel_refl⟩

@[spec high] theorem spec_get (post : Nat → Nat → Prop) :
    ⦃fun s => post s s⦄ (get (m := M)) ⦃post⦄ := ⟨PartialOrder.rel_refl⟩

/-- Matches on state `s` — the discriminant IS the excess state arg. -/
def step : M Unit := do
  let s ← get
  match s with
  | 0 => throw "s is zero"
  | n+1 => set n

def loop (n : Nat) : M Unit := do
  match n with
  | 0 => pure ()
  | n+1 => step; loop n

def Goal (n : Nat) : Prop := ⦃fun s => s = n⦄ loop n ⦃fun _ s => s = 0⦄

end MatchSplit

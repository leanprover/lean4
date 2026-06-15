import Lean
import Std.Tactic.Do
/-!
Port of `Sym/Cases/MatchIota` to the new meta theory.

Pattern matching with a concrete discriminant (the literal argument `v` of `step`). Each
`match v with | 0 => ... | n+1 => ...` iota-reduces during VC generation (no symbolic split).
Because `loop` eventually calls `step 0`, the program throws, so the exceptional postcondition
is left unconstrained (`⊤`).
-/

open Lean Meta Order Std.Internal.Do

set_option mvcgen.warning false

namespace MatchIota

abbrev M := ExceptT String <| StateM Nat

@[spec high] theorem spec_throw (e : String) {post : α → Nat → Prop} {epost : EPost⟨String → Nat → Prop⟩} :
    Triple (epost.head e) (throw (m := M) e) post epost := ⟨PartialOrder.rel_refl⟩

@[spec high] theorem spec_set (x : Nat) {post : PUnit → Nat → Prop} {epost : EPost⟨String → Nat → Prop⟩} :
    Triple (fun _ => post ⟨⟩ x) (set (m := M) x) post epost := ⟨PartialOrder.rel_refl⟩

@[spec high] theorem spec_get (post : Nat → Nat → Prop) {epost : EPost⟨String → Nat → Prop⟩} :
    Triple (fun s => post s s) (get (m := M)) post epost := ⟨PartialOrder.rel_refl⟩

def step (v : Nat) : M Unit := do
  let s ← get
  match v with
  | 0 => throw "v is zero"
  | n+1 => set (s + n + 1); let s ← get; set (s - n)

def loop (n : Nat) : M Unit := do
  match n with
  | 0 => pure ()
  | n+1 => step n; loop n

def Goal (n : Nat) : Prop := ⦃fun s => s = 0⦄ loop n ⦃fun _ s => s = n⦄

end MatchIota

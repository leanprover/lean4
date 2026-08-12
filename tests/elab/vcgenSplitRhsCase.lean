import Std.Tactic.Do
import Std.Internal.Do

/-!
A `@[spec]` theorem whose precondition analyzes a decidable state condition (a conditional jump
testing a flag) reduces its precondition VC to `pre ⊑ if c then E.head jump else <weakest
precondition of the rest>`. `vcgen` splits such a case analysis on the right-hand side of the
entailment, so each branch continues with the condition decided in the local context and the loop
resumes stepping the `wp` the branch exposes.

Covered here: an `ite` at the `Prop` lattice, a `match` on a small inductive with `Prop`-typed
alternatives, and an `ite` at the `Nat → Prop` assertion lattice, where the case analysis is applied
to the state argument `le_of_forall_le` peels.
-/

set_option mvcgen.warning false

open Std.Internal.Do Lean.Order

abbrev M := ExceptT String <| StateM Nat

@[spec] theorem spec_throw (e : String) {post : α → Nat → Prop}
    {E : EPost⟨String → Nat → Prop⟩} :
    ⦃E.head e⦄ (throw (m := M) e) ⦃post; E⦄ := ⟨PartialOrder.rel_refl⟩

@[spec] theorem spec_modify (f : Nat → Nat) {post : PUnit → Nat → Prop} :
    ⦃fun s => post ⟨⟩ (f s)⦄ (modify (m := M) f) ⦃post⦄ := ⟨PartialOrder.rel_refl⟩

/-! ## An `ite` on a decidable state condition -/

def jcc (lim : Nat) : M Unit := do
  let s ← get
  if s > lim then throw "jump" else modify (· + 1)

@[spec] theorem jcc_spec (lim : Nat) {post : PUnit → Nat → Prop}
    {E : EPost⟨String → Nat → Prop⟩} :
    ⦃fun s => if s > lim then E.head "jump" s else post ⟨⟩ (s + 1)⦄
      (jcc lim) ⦃post; E⦄ := by
  vcgen [jcc] <;> grind

def jccProg (lim : Nat) : M Unit := do
  jcc lim
  jcc lim

example (lim : Nat) :
    ⦃fun s => s = 0⦄ jccProg lim ⦃fun _ s => s = 2; epost⟨fun _ s => s ≤ 1⟩⦄ := by
  vcgen [jccProg] <;> grind

/-! ## A `match` on a small inductive -/

inductive Cc where | jump | inc | double

def step (cc : Cc) : M Unit := do
  match cc with
  | .jump => throw "jump"
  | .inc => modify (· + 1)
  | .double => modify (· * 2)

@[spec] theorem step_spec (cc : Cc) {post : PUnit → Nat → Prop}
    {E : EPost⟨String → Nat → Prop⟩} :
    ⦃fun s => match cc with
      | .jump => E.head "jump" s
      | .inc => post ⟨⟩ (s + 1)
      | .double => post ⟨⟩ (s * 2)⦄
      (step cc) ⦃post; E⦄ := by
  vcgen [step] <;> grind

def stepProg (cc : Cc) : M Unit := do
  step cc
  step cc

example (cc : Cc) :
    ⦃fun s => s = 1⦄ stepProg cc ⦃fun _ s => s ≥ 2; epost⟨fun _ s => s = 1⟩⦄ := by
  vcgen [stepProg] <;> grind

/-! ## An `ite` at the assertion lattice, applied to the state argument -/

def jccF (b : Bool) : M Unit := do
  if b then throw "jump" else modify (· + 1)

/-- The branches are assertions rather than propositions, so the precondition VC reads
`pre ⊑ (if b then E.head "jump" else fun s => post () (s + 1)) s`. -/
@[spec] theorem jccF_spec (b : Bool) {post : PUnit → Nat → Prop}
    {E : EPost⟨String → Nat → Prop⟩} :
    ⦃if b then E.head "jump" else fun s => post ⟨⟩ (s + 1)⦄
      (jccF b) ⦃post; E⦄ := by
  vcgen [jccF] <;> simp_all

def jccFProg (b : Bool) : M Unit := do
  jccF b
  jccF b

example (b : Bool) :
    ⦃fun s => s = 0⦄ jccFProg b ⦃fun _ s => s = 2; epost⟨fun _ s => s ≤ 1⟩⦄ := by
  vcgen [jccFProg] <;> grind

/-! ## A `dite`, and a `match` at the assertion lattice -/

def jccD (lim : Nat) : M Unit := do
  let s ← get
  if _ : s > lim then throw "jump" else modify (· + 1)

@[spec] theorem jccD_spec (lim : Nat) {post : PUnit → Nat → Prop}
    {E : EPost⟨String → Nat → Prop⟩} :
    ⦃fun s => if _ : s > lim then E.head "jump" s else post ⟨⟩ (s + 1)⦄
      (jccD lim) ⦃post; E⦄ := by
  vcgen [jccD] <;> grind

def jccDProg (lim : Nat) : M Unit := do
  jccD lim
  jccD lim

example (lim : Nat) :
    ⦃fun s => s = 0⦄ jccDProg lim ⦃fun _ s => s = 2; epost⟨fun _ s => s ≤ 1⟩⦄ := by
  vcgen [jccDProg] <;> grind

def stepF (cc : Cc) : M Unit := do
  match cc with
  | .jump => throw "jump"
  | .inc => modify (· + 1)
  | .double => modify (· * 2)

@[spec] theorem stepF_spec (cc : Cc) {post : PUnit → Nat → Prop}
    {E : EPost⟨String → Nat → Prop⟩} :
    ⦃match cc with
      | .jump => E.head "jump"
      | .inc => fun s => post ⟨⟩ (s + 1)
      | .double => fun s => post ⟨⟩ (s * 2)⦄
      (stepF cc) ⦃post; E⦄ := by
  vcgen [stepF] <;> simp_all

def stepFProg (cc : Cc) : M Unit := do
  stepF cc
  stepF cc

example (cc : Cc) :
    ⦃fun s => s = 1⦄ stepFProg cc ⦃fun _ s => s ≥ 2; epost⟨fun _ s => s = 1⟩⦄ := by
  vcgen [stepFProg] <;> grind

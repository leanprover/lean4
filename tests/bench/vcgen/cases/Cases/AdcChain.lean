import Lean
import Std.Tactic.Do

/-!
Carry-flag chain in `StateM`: a minimal machine with two registers and a carry flag,
where each `adc` adds `rbx` and the carry into `rax` and recomputes the carry from the
overflow condition. Each instruction has an accessor-style spec: the continuation is
quantified over a fresh post-state characterized by one equation per component, so VC
generation accumulates a stratified equation system whose carry chain the discharge
must fold. Minimized from the AeneasVerif/kraken assembly verifier.
-/

open Lean Meta Order Std.WP

namespace AdcChain

set_option mvcgen.warning false

structure S where
  rax : BitVec 64
  rbx : BitVec 64
  cf  : Bool

def movRax (i : BitVec 64) : StateM S Unit := modify fun s => { s with rax := i }

def movRbx (i : BitVec 64) : StateM S Unit := modify fun s => { s with rbx := i }

def adc : StateM S Unit := modify fun s =>
  let v := s.rax + s.rbx + BitVec.ofNat 64 s.cf.toNat
  { rax := v, rbx := s.rbx,
    cf := v.toNat != s.rax.toNat + s.rbx.toNat + s.cf.toNat }

/-! Accessor-style specs: the instruction body is unfolded exactly once, in the spec
proof; VC generation only ever sees the component equations. -/

@[spec] theorem movRax_spec (i : BitVec 64) (post : PUnit → S → Prop) (epost : EPost.Nil) :
    ⦃ fun s => ∀ s' : S, s'.rax = i → s'.rbx = s.rbx → s'.cf = s.cf → post ⟨⟩ s' ⦄
      movRax i ⦃ post; epost ⦄ :=
  ⟨fun _ h => h _ rfl rfl rfl⟩

@[spec] theorem movRbx_spec (i : BitVec 64) (post : PUnit → S → Prop) (epost : EPost.Nil) :
    ⦃ fun s => ∀ s' : S, s'.rax = s.rax → s'.rbx = i → s'.cf = s.cf → post ⟨⟩ s' ⦄
      movRbx i ⦃ post; epost ⦄ :=
  ⟨fun _ h => h _ rfl rfl rfl⟩

@[spec] theorem adc_spec (post : PUnit → S → Prop) (epost : EPost.Nil) :
    ⦃ fun s => ∀ s' : S,
        s'.rax = s.rax + s.rbx + BitVec.ofNat 64 s.cf.toNat →
        s'.rbx = s.rbx →
        s'.cf = ((s.rax + s.rbx + BitVec.ofNat 64 s.cf.toNat).toNat
                  != s.rax.toNat + s.rbx.toNat + s.cf.toNat) →
        post ⟨⟩ s' ⦄
      adc ⦃ post; epost ⦄ :=
  ⟨fun _ h => h _ rfl rfl rfl⟩

def chain : Nat → StateM S Unit
  | 0 => pure ()
  | n+1 => do adc; chain n

def prog (n : Nat) : StateM S Unit := do
  movRax 1
  movRbx 3
  chain n

def Goal (n : Nat) : Prop :=
  ⦃ fun _ => True ⦄ prog n ⦃ fun _ s => s.rax = BitVec.ofNat 64 (1 + 3 * n) ⦄

end AdcChain

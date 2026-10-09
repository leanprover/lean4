import Lean
import Std.WP

/-!
`poke v` writes `v` at `mem ptr`, so it frames `fun s => s.mem 5 = 7` exactly in the states with
`ptr ≠ 5`. The guard of the `WP.Frames` side goal fixes the state at `poke 1` to
`{ ptr := 3, mem := s.mem }`, and that guard makes `poke_frames` provable.
-/

set_option experimental.vcgen true
set_option grind.warning false

open Lean Order Std WP

structure St where
  ptr : Nat
  mem : Nat → Nat

inductive Instr where
  | setPtr (p : Nat)
  | poke (v : Nat)

def Instr.step : Instr → St → St
  | .setPtr p, s => { s with ptr := p }
  | .poke v, s => { s with mem := fun a => if a = s.ptr then v else s.mem a }

def run : List Instr → St → St
  | [], s => s
  | i :: p, s => run p (i.step s)

instance : WP Instr Unit (St → Prop) Unit where
  trans i := ⟨fun Q _ s => Q () (i.step s)⟩
  trans_monotone _ := fun _ _ _ _ _ hQ _ h => hQ () _ h

instance : WP (List Instr) Unit (St → Prop) Unit where
  trans p := ⟨fun Q _ s => Q () (run p s)⟩
  trans_monotone _ := fun _ _ _ _ _ hQ _ h => hQ () _ h

section
variable {Q : Unit → St → Prop} {E : Unit}

@[spec] theorem nil_spec : ⦃ fun s => Q () s ⦄ ([] : List Instr) ⦃ Q; E ⦄ := ⟨fun _ h => h⟩

@[spec] theorem cons_spec (i : Instr) (p : List Instr) :
    ⦃ wp i (fun _ => wp p Q E) E ⦄ (i :: p) ⦃ Q; E ⦄ := ⟨fun _ h => h⟩

@[spec] theorem setPtr_spec (p : Nat) :
    ⦃ fun s => Q () { s with ptr := p } ⦄ Instr.setPtr p ⦃ Q; E ⦄ := ⟨fun _ h => h⟩

@[spec] theorem poke_spec (p v : Nat) :
    ⦃ fun s => s.ptr = p ⦄ Instr.poke v ⦃ fun _ s => s.mem p = v ⦄ :=
  ⟨fun s h => by simp [wp, WP.trans, Instr.step, h]⟩

theorem poke_frames {v : Nat} {F P : St → Prop} (hF : F = fun s => s.mem 5 = 7)
    (h : ∀ t, P t ⊑ ⌜t.ptr ≠ 5⌝) : WP.Frames meet (Instr.poke v) F P := by
  subst hF
  constructor
  intro Q E s hs
  simp only [meet_apply, meet_prop_eq_and] at hs
  obtain ⟨hP, hF, hwp⟩ := hs
  have hne := h s hP
  simp only [CompleteLattice.ofProp_prop_eq] at hne
  show ((fun s => s.mem 5 = 7) ⊓ Q ()) (Instr.step (.poke v) s)
  simp only [meet_apply, meet_prop_eq_and, Instr.step]
  exact ⟨by simp [Ne.symm hne, hF], hwp⟩

end

/--
trace: s✝ : St
a✝ : s✝.mem 5 = 7
⊢ WP.Frames meet (Instr.poke 1) (fun s => s.mem 5 = 7) fun u => ⌜u = { ptr := 3, mem := s✝.mem }⌝ ⊓ ⊤
-/
#guard_msgs (trace) in
theorem guard_point_frame :
    ⦃ fun s => s.mem 5 = 7 ⦄ [Instr.setPtr 3, Instr.poke 1]
    ⦃ fun _ s => s.mem 5 = 7 ∧ s.mem 3 = 1 ⦄ := by
  vcgen frames | Instr.poke _ => fun s => s.mem 5 = 7
  case vc1 => trace_state; grind [poke_frames]
  all_goals grind

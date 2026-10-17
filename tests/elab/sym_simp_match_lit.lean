/-!
Tests that `Sym.simp` reduces `match` expressions whose discriminants are literals.
The match compiler decides literal patterns with `decEq`, so `Sym.simp` rewrites with the
match equations, and the simplifier continues on the selected alternative.
-/

inductive E where | a | b | c

example : (match "b" with | "a" => 1 | "b" => 2 | _ => 3) = 2 := by
  sym => simp

-- The equation of the catch-all alternative has the overlap hypotheses `"c" = "a" → False`
-- and `"c" = "b" → False`.
example : (match "c" with | "a" => 1 | "b" => 2 | _ => 3) = 3 := by
  sym => simp

example (x : Nat × Nat) : (match "b", x with | "a", _ => 1 | "b", p => p.1 | _, _ => 0) = x.1 := by
  sym => simp

example : (match 2 with | 1 => 1 | 2 => 2 | _ => 3) = 2 := by
  sym => simp

example : (match 5 with | 1 => 1 | 2 => 2 | _ => 3) = 3 := by
  sym => simp

example : (match 'b' with | 'a' => 1 | 'b' => 2 | _ => 3) = 2 := by
  sym => simp

example : (match E.c with | .a => 1 | .b => 2 | _ => 3) = 3 := by
  sym => simp

-- The discriminant `x` is not a literal, so the `match` stays.
/-- error: `Sym.simp` made no progress -/
#guard_msgs in
example (x : String) : (match x with | "a" => 1 | "b" => 2 | _ => 3) = 3 := by
  sym => simp

/-! The second discriminant is a structure instance. The selected alternative is simplified further. -/

structure Regs where
  r8 : Nat
  rdi : Nat

def Regs.set8 (r : Regs) (v : Nat) : Regs := { r with r8 := v }

theorem Regs.rdi_set8 (r : Regs) (v : Nat) : (r.set8 v).rdi = r.rdi := rfl

structure State where
  regs : Regs
  pc : Nat

theorem State.regs_mk (r : Regs) (pc : Nat) : (State.mk r pc).regs = r := rfl
theorem State.pc_mk (r : Regs) (pc : Nat) : (State.mk r pc).pc = pc := rfl

example (s : State) (v : Nat) :
    match ".loop128", { s with regs := s.regs.set8 v } with
    | ".loop", s' => s'.pc = 0
    | ".loop128", s' => s'.regs.rdi = s.regs.rdi ∧ s'.pc = s.pc
    | _, _ => False := by
  sym => simp [State.regs_mk, State.pc_mk, Regs.rdi_set8, and_self]

example (s : State) (v : Nat) :
    match ".exit", { s with regs := s.regs.set8 v } with
    | ".loop", s' => s'.pc = 0
    | ".loop128", _ => False
    | _, s' => s'.regs.rdi = s.regs.rdi := by
  sym => simp [State.regs_mk, Regs.rdi_set8]

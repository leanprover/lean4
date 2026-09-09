/-!
Tests `cbv` reduction of stacked projections over a dependent projection whose
struct only reaches constructor form through a propositional rewrite (e.g. the
equations of a well-founded recursive definition). No single projection level
admits a homogeneous `Eq` proof — the type of the intermediate dependent
projection mentions the stuck struct — but the composite projection function is
non-dependent, so `cbv` can rewrite the whole projection spine at once via
`congrArg`.
-/

structure Payload (α : Type) where
  val : α
  len : Nat

/-- Well-founded recursion: unfolds only propositionally, never definitionally. -/
def mkPayload : Nat → Σ α : Type, Payload α
  | 0 => ⟨Bool, ⟨true, 0⟩⟩
  | n + 1 => mkPayload n
termination_by n => n

-- Single non-dependent projection: handled by the per-level `congrArg` path.
example : (mkPayload 3).fst = Bool := by cbv

-- Non-dependent `.len` stacked over the dependent `.snd`: needs the spine path.
example : (mkPayload 3).snd.len = 0 := by cbv

structure Inner (α : Type) where
  a : α
  m : Nat

structure Outer (α : Type) where
  inn : Inner α
  k : Nat

def mkOuter : Nat → Σ α : Type, Outer α
  | 0 => ⟨Bool, ⟨⟨true, 7⟩, 5⟩⟩
  | n + 1 => mkOuter n
termination_by n => n

-- Three-level spine: both intermediate composites (`.snd`, `.snd.inn`) are dependent.
example : (mkOuter 2).snd.inn.m = 7 := by cbv
example : (mkOuter 2).snd.k = 5 := by cbv

-- Stacked projections inside a larger ground computation.
example : (mkOuter 2).snd.inn.m + (mkPayload 1).snd.len + (mkOuter 0).snd.k = 12 := by cbv

-- Base is `@[cbv_opaque]`: kernel reduction of the projection is suppressed, so
-- the constructor form is only available through the `@[cbv_eval]` rewrite.
@[cbv_opaque] def opaquePayload : Σ α : Type, Payload α := ⟨Bool, ⟨true, 5⟩⟩

@[cbv_eval] theorem opaquePayload_eq : opaquePayload = ⟨Bool, ⟨true, 5⟩⟩ := rfl

example : opaquePayload.snd.len = 5 := by cbv

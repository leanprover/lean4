module

public structure State where
  private count : Nat

private example {P : State → Prop} (h : P ⟨State.count s⟩) :
    P ⟨State.count s⟩ := by
  set_option trace.Meta.Tactic.simp true in
  set_option trace.Debug.Meta.Tactic.simp true in
  set_option trace.Debug.Meta.Tactic.simp.congr true in
  set_option trace.Meta.realizeConst true in
  set_option trace.congr.thm true in
  simp [*]

private example {P : State → Prop} (h : P ⟨State.count s⟩) :
    P ⟨State.count s⟩ := by
  omega

private example {P : State → Prop} (h : P ⟨State.count s⟩) :
    P ⟨State.count s⟩ := by
  grind

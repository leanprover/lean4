module

public import Module.UnfoldNonRecBase

/-!
`unfold` on a non-recursive definition gives the same goal whether or not its `eq_def` theorem has
been realized, and independently of whether an upstream realization is visible here.
-/

/--
trace: k n y : Nat
⊢ (match UnfoldT.b n with
    | UnfoldT.a => 0
    | UnfoldT.b n =>
      have x := n + k;
      x * x) =
    y
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example (k n y : Nat) : unfoldF k (.b n) = y := by
  unfold unfoldF
  trace_state
  sorry

/--
trace: k n y : Nat
⊢ (match UnfoldT.b n with
    | UnfoldT.a => 0
    | UnfoldT.b n =>
      have x := n + k;
      x * x) =
    y
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example (k n y : Nat) : unfoldG k (.b n) = y := by
  unfold unfoldG
  trace_state
  sorry

/--
trace: k n y : Nat
⊢ (match UnfoldT.b n with
    | UnfoldT.a => 0
    | UnfoldT.b n =>
      have x := n + k;
      x * x) =
    y
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example (k n y : Nat) : unfoldH k (.b n) = y := by
  unfold unfoldH
  trace_state
  sorry

/-! Realizing `eq_def` locally does not change the result either. -/

/--
trace: k n y : Nat
this :
  ∀ (k : Nat) (x : UnfoldT),
    unfoldH k x =
      match x with
      | UnfoldT.a => 0
      | UnfoldT.b n =>
        have x := n + k;
        x * x
⊢ (match UnfoldT.b n with
    | UnfoldT.a => 0
    | UnfoldT.b n =>
      have x := n + k;
      x * x) =
    y
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example (k n y : Nat) : unfoldH k (.b n) = y := by
  have := @unfoldH.eq_def
  unfold unfoldH
  trace_state
  sorry

/-! Recursive definitions are still unfolded using `eq_def`, which reduces the matcher. -/

/--
trace: k n y : Nat
⊢ (have x := unfoldR k (UnfoldT.b n);
    x * x) =
    y
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example (k n y : Nat) : unfoldR k (.b (n + 1)) = y := by
  unfold unfoldR
  trace_state
  sorry

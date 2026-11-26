module

/-! Auxiliary module for `Module.UnfoldNonRec`. -/

public section

inductive UnfoldT where
  | a | b (n : Nat)

/-- `unfoldF.eq_def` is realized inside the proof of `unfoldF_ge` only. -/
@[expose] def unfoldF (k : Nat) : UnfoldT → Nat
  | .a => 0
  | .b n =>
    let x := n + k
    x * x

theorem unfoldF_ge (k : Nat) (t : UnfoldT) : 0 ≤ unfoldF k t := by
  fun_cases unfoldF with
  | case1 => simp
  | case2 n x => simp

/-- `unfoldG.eq_def` is realized outside of a proof and so is visible to importers. -/
@[expose] def unfoldG (k : Nat) : UnfoldT → Nat
  | .a => 0
  | .b n =>
    let x := n + k
    x * x

def unfoldG_eq_def := @unfoldG.eq_def

/-- `unfoldH.eq_def` is never realized. -/
@[expose] def unfoldH (k : Nat) : UnfoldT → Nat
  | .a => 0
  | .b n =>
    let x := n + k
    x * x

/-- A recursive definition, for which `unfold` uses `unfoldR.eq_def`. -/
@[expose] def unfoldR (k : Nat) : UnfoldT → Nat
  | .a => 0
  | .b 0 => k
  | .b (n + 1) =>
    let x := unfoldR k (.b n)
    x * x

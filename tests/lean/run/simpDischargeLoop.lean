open Nat

def double : Nat → Nat
  | zero   => 0
  | succ n => succ (succ (double n))

theorem double.inj : double n = double m → n = m := by
  intro h
  induction n generalizing m with
  | zero => cases m <;> trivial
  | succ n ih =>
    cases m with
    | zero   => contradiction
    | succ m =>
      simp [double] at h |-
      apply ih h

theorem double.inj' : double n = double m → n = m := by
  intro h
  induction n generalizing m with
  | zero => cases m <;> trivial
  | succ n ih =>
    cases m with
    | zero => contradiction
    | succ m =>
      simp
      apply ih
      simp_all [double]

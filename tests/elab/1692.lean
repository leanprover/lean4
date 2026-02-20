import Lean.Hygiene

def otherInhabited : Inhabited Nat := ⟨42⟩

def f := Id.run do
  let ⟨n⟩ ← pure otherInhabited
  -- do-notation expands to `pure otherInhabited >>= fun x : Inhabited Nat => ...`
  -- the `x : Inhabited Nat` should not be available for TC synth (i.e., `default` should be 0)
  return default + n

example : f = 42 := rfl

open Lean
def g : Syntax :=
  let rec stx : Syntax := Unhygienic.run `(f 0 1)
  let stx := stx
  match stx with
  | `(f $_args*) => ‹Syntax› -- should not resolve to tmp var created by stx matcher
  | _ => default

example : g = g.stx := rfl

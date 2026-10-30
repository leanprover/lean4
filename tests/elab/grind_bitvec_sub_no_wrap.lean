import Lean
/-!
`grind` translates `(x - y).toNat` for `x y : BitVec w` to `Nat`. If the context gives
`y.toNat ≤ x.toNat`, the subtraction does not wrap around, and the proof needs no
quotient variable for `2 ^ w`.

The theorem `subs` has eight such subtractions. Its proof must have no instance of the
general `%` encoding `Int.Internal.Linear.ediv_emod`.
-/

open Lean in
/--
The number of distinct applications of `c` in the proof of `thm`, including the auxiliary
lemmas `thm._proof_*` that the proof refers to.
-/
partial def countIn (thm c : Name) : CoreM Nat := do
  let env ← getEnv
  let rec go (e : Expr) : StateM (Std.HashSet Expr) Unit := do
    if (← get).contains e then return
    modify (·.insert e)
    match e with
    | .const n _ =>
      if thm.isPrefixOf n && n != thm then
        if let some (.thmInfo info) := env.find? n then go info.value
    | .app f a => go f; go a
    | .lam _ t b _ | .forallE _ t b _ => go t; go b
    | .letE _ t v b _ => go t; go v; go b
    | .mdata _ b | .proj _ _ b => go b
    | _ => pure ()
  let some (.thmInfo info) := env.find? thm | throwError "unknown theorem {thm}"
  let ((), s) := (go info.value).run {}
  return s.fold (fun n e => if e.isAppOf c then n + 1 else n) 0

set_option linter.unusedVariables false in
theorem subs (x₀ x₁ x₂ x₃ x₄ x₅ x₆ x₇ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ : BitVec 64)
    (h₀ : y₀.toNat ≤ x₀.toNat) (h₁ : y₁.toNat ≤ x₁.toNat) (h₂ : y₂.toNat ≤ x₂.toNat)
    (h₃ : y₃.toNat ≤ x₃.toNat) (h₄ : y₄.toNat ≤ x₄.toNat) (h₅ : y₅.toNat ≤ x₅.toNat)
    (h₆ : y₆.toNat ≤ x₆.toNat) (h₇ : y₇.toNat ≤ x₇.toNat) :
    (x₀ - y₀).toNat + (x₁ - y₁).toNat + (x₂ - y₂).toNat + (x₃ - y₃).toNat +
      (x₄ - y₄).toNat + (x₅ - y₅).toNat + (x₆ - y₆).toNat + (x₇ - y₇).toNat +
      (y₀.toNat + y₁.toNat + y₂.toNat + y₃.toNat + y₄.toNat + y₅.toNat + y₆.toNat + y₇.toNat) =
    x₀.toNat + x₁.toNat + x₂.toNat + x₃.toNat + x₄.toNat + x₅.toNat + x₆.toNat + x₇.toNat := by
  grind

/-- info: 0 -/
#guard_msgs in
#eval countIn ``subs ``Int.Internal.Linear.ediv_emod

-- Twenty nested subtractions: each one gives one instance of one rule.
example (x : BitVec 64) (h : 210 ≤ x.toNat) :
    ((((((((((((((((((((x - 1) - 2) - 3) - 4) - 5) - 6) - 7) - 8) - 9) - 10) - 11) - 12) - 13)
      - 14) - 15) - 16) - 17) - 18) - 19) - 20).toNat = x.toNat - 210 := by
  grind

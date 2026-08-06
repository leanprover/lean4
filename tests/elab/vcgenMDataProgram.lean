import Std.Internal.Do
import Lean
import Std
import Std.Tactic.Do

set_option mvcgen.warning false

/-! `vcgen` must classify a program wrapped in an `mdata` node, such as the
`save_info` annotation left behind by spec elaboration. -/

open Std.Internal.Do Lean.Order

/-- Wrap a term in a `save_info` `mdata` node, exactly what spec elaboration leaves behind. -/
syntax "mdata% " term : term

open Lean Elab Term in
elab_rules : term <= ty
  | `(mdata% $t) => do
    return .mdata (KVMap.empty.insert `save_info (.ofNat 1)) (← elabTerm t ty)

-- `match` program.
example (c : Bool) :
    ⦃fun _ => True⦄ (mdata% (match c with | true => pure 1 | false => pure 2) : StateM Nat Nat)
    ⦃fun _ _ => True⦄ := by
  vcgen

-- Bare `pure` program.
example :
    ⦃fun _ => True⦄ (mdata% (pure 1) : StateM Nat Nat)
    ⦃fun _ _ => True⦄ := by
  vcgen

-- `ite` program.
example (c : Bool) :
    ⦃fun _ => True⦄ (mdata% (if c then pure 1 else pure 2) : StateM Nat Nat)
    ⦃fun _ _ => True⦄ := by
  vcgen

-- `let` program.
example :
    ⦃fun _ => True⦄ (mdata% (let x := 1; pure x) : StateM Nat Nat)
    ⦃fun _ _ => True⦄ := by
  vcgen

-- `do` bind sequence over state operations.
example :
    ⦃fun _ => True⦄ (mdata% (do let x ← get; modify (· + x); pure x) : StateM Nat Nat)
    ⦃fun _ _ => True⦄ := by
  vcgen

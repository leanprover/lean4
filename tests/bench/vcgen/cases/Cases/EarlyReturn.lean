import Lean
import Std.Tactic.Do

/-!
A `for` loop with `k` `return` sites and code after the loop, for `k` = 10, 20 and 40. `vcgen`
checks each `return` against the postcondition of the function, so the cost grows linearly in `k`.
-/

open Lean Meta Order Std.WP

set_option experimental.intrinsic true

namespace EarlyReturn

/-- `early_return_step f k` defines `f`, whose loop has the `return` sites `x = 0, …, x = k - 1`. -/
syntax "early_return_step " ident num : command

macro_rules
  | `(early_return_step $name $k) => do
    let mut items : Array (TSyntax ``Lean.Parser.Term.doSeqItem) := #[]
    for i in [0:k.getNat] do
      let lit := Syntax.mkNumLit (toString i)
      items := items.push (← `(Lean.Parser.Term.doSeqItem| if x = $lit then return acc + $lit))
    items := items.push (← `(Lean.Parser.Term.doSeqItem| acc := acc + x))
    let body ← `(Lean.Parser.Term.doSeq| $items*)
    `(def $name (xs : List Nat) : StateM Nat Nat := do
        let mut acc := 0
        for x in xs invariant _ _ _ => True do $body
        let s ← get
        set (s + acc)
        return acc + s + 1)

early_return_step step10 10
early_return_step step20 20
early_return_step step40 40

def Goal (n : Nat) : Prop :=
  ∀ xs, ⦃fun _ => True⦄ (if n = 10 then step10 xs else if n = 20 then step20 xs else step40 xs)
    ⦃fun _ _ => True⦄

end EarlyReturn

import Cases.GetThrowSet
import Driver

open Lean Parser Meta Elab Tactic Sym Std Do SpecAttr
open GetThrowSet

-- Copy Goal into a separate namespace so the benchmark label reads `GetThrowSetGrind(n)`
-- instead of colliding with the `GetThrowSet(n)` label in vcgen_get_throw_set.
namespace GetThrowSetGrind
def Goal (n : Nat) : Prop := ⦃fun s => ⌜s = 0⌝⦄ loop n ⦃⇓_ s => ⌜s = n⌝⦄
end GetThrowSetGrind

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

-- Benchmark `mvcgen' with grind`: grind integrated into VCGen loop for incremental
-- context internalization. This avoids O(n) re-internalization per VC.
-- `simplifying_assumptions [Nat.add_assoc]` here speeds up grind and kernel checking by a factor
-- of 2 because long chains `s + 1 + ... + 1` are collapsed into `s + n`.
#eval runBenchUsingTactic ``GetThrowSetGrind.Goal [``loop, ``step] `(tactic| mvcgen' simplifying_assumptions [Nat.add_assoc] with grind) `(tactic| fail)
  [50, 100, 150]

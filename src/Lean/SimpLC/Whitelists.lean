import Lean.SimpLC.Whitelists.Root
import Lean.SimpLC.Whitelists.Array
import Lean.SimpLC.Whitelists.BitVec
import Lean.SimpLC.Whitelists.Bool
import Lean.SimpLC.Whitelists.Fin
import Lean.SimpLC.Whitelists.List
import Lean.SimpLC.Whitelists.Monad
import Lean.SimpLC.Whitelists.Nat
import Lean.SimpLC.Whitelists.Option
import Lean.SimpLC.Whitelists.Prod
import Lean.SimpLC.Whitelists.Std
import Lean.SimpLC.Whitelists.Subtype
import Lean.SimpLC.Whitelists.Sum

set_option maxHeartbeats 0

/-
The actual checks happen in `tests/lean/run/simplc.lean`.
These commented out commands remain here for convenience while debugging.
-/

/-
Ideally downstream libraries would preserve the fact that the
`simp_lc check in <...builtin types ...>` command below succeeds
(possibly by adding further whitelists and ignores).
Even better, they would add `_root_` to the check as well,
if they do not intentionally occupy the root namespace.
-/
-- #guard_msgs (drop info) in
-- simp_lc check in String Char Float USize UInt64 UInt32 UInt16 UInt8 PLift ULift Prod Sum Range
--   Subtype ByteArray FloatArray List Option Array Int Nat Bool Id
--   Monad LawfulFunctor LawfulApplicative LawfulMonad LawfulSingleton Std

/-
Check *everything*.
-/
-- #time
-- #guard_msgs (drop info) in
-- simp_lc check

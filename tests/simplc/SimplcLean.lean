import SimplcLean._root_
import SimplcLean.Array
import SimplcLean.BitVec
import SimplcLean.Bool
import SimplcLean.Fin
import SimplcLean.List
import SimplcLean.Monad
import SimplcLean.Nat
import SimplcLean.Option
import SimplcLean.Prod
import SimplcLean.Std
import SimplcLean.Subtype

-- It would be lovely if downstream libraries could preserve this invariant,
-- i.e. not further breaking confluence in the namespaces for basic data types.
#guard_msgs (drop info) in
simp_lc check in String Char Float USize UInt64 UInt32 UInt16 UInt8 PLift ULift Prod Sum Range Subtype ByteArray FloatArray
  List Option Array Int Nat Bool Id Monad LawfulMonad LawfulSingleton Std
-- Libraries could also aspire to adding `_root_` to the above check!

set_option maxHeartbeats 0 in
#guard_msgs (drop info) in
simp_lc check

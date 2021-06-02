import Std.Data.PersistentHashMap

open Std
def m : PersistentHashMap Nat Nat :=
let m : PersistentHashMap Nat Nat := {};
m.insert 1 1

def natDiffHash : Hashable Nat :=
⟨fun n => UInt64.ofNat $ n+10⟩

-- The following example should fail since the `Hashable` instance used to create `m` is not `natDiffHash`
#eval @PersistentHashMap.find? Nat Nat _ natDiffHash m 1

set_option trace.Meta.synthInstance.cache true
/--
trace: [Meta.synthInstance.cache] cached: HAppend (List Nat) (List Nat) (List Nat)
[Meta.synthInstance.cache] cached: HAppend (List Nat) (List Nat) (List Nat)
---
trace: [Meta.synthInstance.cache] cached: HAppend (List Nat) (List Nat) (List Nat)
[Meta.synthInstance.cache] cached: HAppend (List Nat) (List Nat) (List Nat)
---
trace: [Meta.synthInstance.cache] cached: HAppend (List Nat) (List Nat) (List Nat)
[Meta.synthInstance.cache] cached: HAppend (List Nat) (List Nat) (List Nat)
---
trace: [Meta.synthInstance.cache] new: HAppend (List Nat) (List Nat) (List Nat)
[Meta.synthInstance.cache] cached: HAppend (List Nat) (List Nat) (List Nat)
-/
#guard_msgs (ordering := sorted) in
def ex (a : List Nat) : List Nat :=
  a ++ a ++ a ++ a ++ a

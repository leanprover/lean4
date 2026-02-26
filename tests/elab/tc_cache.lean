/-
Type class resolution cache.
Recall that we normalize keys for type class with output parameters only when the input type
contains metavariables. This is why in the following example we sold
```
new: HAppend (List Nat) (List Nat) ?_
```
and
```
new: HAppend (List Nat) (List Nat) (List Nat)
```
-/

set_option pp.mvars.anonymous false
set_option trace.Meta.synthInstance.cache true
/--
trace: [Meta.synthInstance.cache] cached: HAppend (List Nat) (List Nat) (List Nat)
[Meta.synthInstance.cache] cached: HAppend (List Nat) (List Nat) ?_
---
trace: [Meta.synthInstance.cache] cached: HAppend (List Nat) (List Nat) (List Nat)
[Meta.synthInstance.cache] cached: HAppend (List Nat) (List Nat) ?_
---
trace: [Meta.synthInstance.cache] cached: HAppend (List Nat) (List Nat) (List Nat)
[Meta.synthInstance.cache] new: HAppend (List Nat) (List Nat) ?_
---
trace: [Meta.synthInstance.cache] new: HAppend (List Nat) (List Nat) (List Nat)
[Meta.synthInstance.cache] cached: HAppend (List Nat) (List Nat) ?_
-/
#guard_msgs (ordering := sorted) in
def ex (a : List Nat) : List Nat :=
  a ++ a ++ a ++ a ++ a

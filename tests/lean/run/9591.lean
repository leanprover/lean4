/-!
# Error recovery for anonymous constructor notation
https://github.com/leanprover/lean4/issues/9591

When errToSorry is enabled, and too few arguments are provided, now it inserts `sorry`s
while logging an error (rather than throwing an error).
-/

/--
error: Insufficient number of fields for `⟨...⟩` constructor: Constructor `Prod.mk` has 2 explicit field, but none were provided
---
info: have this := (sorry, sorry);
this : Nat × Nat
-/
#guard_msgs in #check show Nat × Nat from ⟨⟩

/--
error: Insufficient number of fields for `⟨...⟩` constructor: Constructor `Prod.mk` has 2 explicit field, but only 1 was provided
---
info: have this := (2, sorry);
this : Nat × Nat
-/
#guard_msgs in #check show Nat × Nat from ⟨2⟩

/--
error: Insufficient number of fields for `⟨...⟩` constructor: Constructor `Prod.mk` has 2 explicit field, but only 1 was provided
---
error: Unknown constant `Nat.su`

Note: Inferred this name from the expected resulting type of `.su`:
  Nat
---
info: have this := (sorry, sorry);
this : Nat × Nat
-/
#guard_msgs in #check show Nat × Nat from ⟨.su⟩

/--
info: have this := (2, 3);
this : Nat × Nat
-/
#guard_msgs in #check show Nat × Nat from ⟨2,3⟩

/-!
The `first` tactic disables errToSorry, which is how the first `exact` throws an exception rather than logging an error.
-/
/--
info: have this := (2, 3);
this : Nat × Nat
-/
#guard_msgs in #check show Nat × Nat by first | exact ⟨1⟩ | exact ⟨2,3⟩

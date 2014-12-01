import logic
open tactic

definition simple := apply trivial

tactic_hint simple

theorem foo : true
theorem foo2 (a : Prop) : a :
theorem foo3 : true

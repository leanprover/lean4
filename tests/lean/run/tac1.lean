import tools.tactic logic
open tactic

definition mytac := apply @and.intro; apply @eq.refl

check @mytac

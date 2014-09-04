import tools.tactic
open tactic

definition mytac := apply @and_intro; apply @refl

check @mytac

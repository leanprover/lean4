variable x : Nat

set_opaque x true.

print "before import"
(*
local env = get_environment()
env:import("tstblafoo.lean")
*)

print "before load1"
(*
local env = get_environment()
env:load("tstblafoo.lean")
*)

print "before load2"
(*
local env = get_environment()
env:load("fake1.olean")
*)

print "before load3"
(*
local env = get_environment()
env:load("fake2.olean")
*)

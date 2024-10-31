import Lean.SimpLC.Whitelists

-- Warning: this takes about 15 minutes to run!
set_option maxHeartbeats 0 in
#guard_msgs (drop info) in
simp_lc check

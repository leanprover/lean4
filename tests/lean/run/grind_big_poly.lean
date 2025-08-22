module
/--
trace: [grind.issues] maximum recursion depth has been reached
    use `set_option maxRecDepth <num>` to increase limit
    use `set_option diagnostics true` to get diagnostic information
-/
#guard_msgs (drop error, trace) in
set_option trace.grind.issues true in
example (x y z w : Int) : (x + y + z + w)^5000 - 1 = 0 := by
  grind -- should not crash

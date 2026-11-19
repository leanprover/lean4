module

/-- info: 10000000 -/
#guard_msgs in
#eval (List.range 10000000).flatMapM (m := Id) (fun d => pure [d]) |>.length

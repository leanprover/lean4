/-- warning: declaration uses 'sorry' -/
#guard_msgs in
set_option debug.sorryProps true in
example : 1 = 2 := rfl

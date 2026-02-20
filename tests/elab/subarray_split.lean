/-!
# Tests for Subarray Splitting

The tests in this file check the basic splitting operations on subarrays.
-/

def abc' := #['a', 'b', 'c']
def abc := abc'.toSubarray


/-!

## Split

Splitting at various indices yields all the input elements the right number of times.

-/
/-- info: (#[].toSubarray, #[1, 2, 3, 4].toSubarray) -/
#guard_msgs in
#eval (#[1,2,3,4].toSubarray.split 0)

/-- info: (#[1].toSubarray, #[2, 3, 4].toSubarray) -/
#guard_msgs in
#eval (#[1,2,3,4].toSubarray.split 1)

/-- info: (#[1, 2].toSubarray, #[3, 4].toSubarray) -/
#guard_msgs in
#eval (#[1,2,3,4].toSubarray.split 2)

/-- info: (#[1, 2, 3].toSubarray, #[4].toSubarray) -/
#guard_msgs in
#eval (#[1,2,3,4].toSubarray.split 3)

/-- info: (#[1, 2, 3, 4].toSubarray, #[].toSubarray) -/
#guard_msgs in
#eval (#[1,2,3,4].toSubarray.split ⟨4, by decide⟩)

/-- info: (#[2, 3].toSubarray, #[4].toSubarray) -/
#guard_msgs in
#eval (#[1,2,3,4].toSubarray (start := 1) |>.split ⟨2, by decide⟩)


/-- info: (#[].toSubarray, #['a', 'b', 'c'].toSubarray) -/
#guard_msgs in
#eval abc.split 0

/-- info: (#['a'].toSubarray, #['b', 'c'].toSubarray) -/
#guard_msgs in
#eval abc.split 1

/-- info: (#['a', 'b'].toSubarray, #['c'].toSubarray) -/
#guard_msgs in
#eval abc.split 2

/-- info: (#['a', 'b', 'c'].toSubarray, #[].toSubarray) -/
#guard_msgs in
#eval abc.split 3

/-!
## Take and Drop
-/

/-- info: #[].toSubarray -/
#guard_msgs in
#eval #[1,2,3].toSubarray.take 0

/-- info: #[1].toSubarray -/
#guard_msgs in
#eval #[1,2,3].toSubarray.take 1
/-- info: #[1, 2].toSubarray -/
#guard_msgs in
#eval #[1,2,3].toSubarray.take 2
/-- info: #[1, 2, 3].toSubarray -/
#guard_msgs in
#eval #[1,2,3].toSubarray.take 100

/-- info: #[1, 2, 3].toSubarray -/
#guard_msgs in
#eval #[1,2,3].toSubarray.drop 0

/-- info: #[2, 3].toSubarray -/
#guard_msgs in
#eval #[1,2,3].toSubarray.drop 1

/-- info: #[3].toSubarray -/
#guard_msgs in
#eval #[1,2,3].toSubarray.drop 2

/-- info: #[].toSubarray -/
#guard_msgs in
#eval #[1,2,3].toSubarray.drop 100

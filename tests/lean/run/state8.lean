inductive States | s0 | s1 | s2 | s3 | s4 | s5 | s6 | s7
open States
def f : States → States → States
| s0, s0 => s0
| s0, s1 => s0
| s0, s2 => s0
| s0, s3 => s0
| s0, s4 => s0
| s0, s5 => s0
| s0, s6 => s0
| s0, s7 => s0
| s1, s0 => s0
| s1, s1 => s0
| s1, s2 => s0
| s1, s3 => s0
| s1, s4 => s0
| s1, s5 => s0
| s1, s6 => s0
| s1, s7 => s0
| s2, s0 => s0
| s2, s1 => s0
| s2, s2 => s0
| s2, s3 => s0
| s2, s4 => s0
| s2, s5 => s0
| s2, s6 => s0
| s2, s7 => s0
| s3, s0 => s0
| s3, s1 => s0
| s3, s2 => s0
| s3, s3 => s0
| s3, s4 => s0
| s3, s5 => s0
| s3, s6 => s0
| s3, s7 => s0
| s4, s0 => s0
| s4, s1 => s0
| s4, s2 => s0
| s4, s3 => s0
| s4, s4 => s0
| s4, s5 => s0
| s4, s6 => s0
| s4, s7 => s0
| s5, s0 => s0
| s5, s1 => s0
| s5, s2 => s0
| s5, s3 => s0
| s5, s4 => s0
| s5, s5 => s0
| s5, s6 => s0
| s5, s7 => s0
| s6, s0 => s0
| s6, s1 => s0
| s6, s2 => s0
| s6, s3 => s0
| s6, s4 => s0
| s6, s5 => s0
| s6, s6 => s0
| s6, s7 => s0
| s7, s0 => s0
| s7, s1 => s0
| s7, s2 => s0
| s7, s3 => s0
| s7, s4 => s0
| s7, s5 => s0
| s7, s6 => s0
| s7, s7 => s0
set_option maxHeartbeats 0
example : ∀ x y z, f (f (f s0 x) y) z = f (f x z) (f y z) := by
 intros x y z
 cases x <;> cases y <;> cases z <;> rfl

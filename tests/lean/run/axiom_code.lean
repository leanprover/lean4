constant ax : nat
noncomputable def test : nat → nat
| 0     := ax
| (n+1) := test n

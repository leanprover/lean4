inductive day
| monday | tuesday | wednesday | thursday | friday | saturday | sunday

open day

definition next_weekday : day → day
| monday    := tuesday
| tuesday   := wednesday
| wednesday := thursday
| thursday  := friday
| friday    := monday
| saturday  := monday
| sunday    := monday

example : next_weekday (next_weekday monday) = wednesday :=
rfl

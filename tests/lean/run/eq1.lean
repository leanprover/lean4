inductive day :=
monday | tuesday | wednesday | thursday | friday | saturday | sunday

open day

definition next_weekday : day → day
| next_weekday monday    := tuesday
| next_weekday tuesday   := wednesday
| next_weekday wednesday := thursday
| next_weekday thursday  := friday
| next_weekday friday    := monday
| next_weekday saturday  := monday
| next_weekday sunday    := monday

example : next_weekday (next_weekday monday) = wednesday :=
rfl

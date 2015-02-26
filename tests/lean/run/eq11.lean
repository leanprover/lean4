inductive day :=
monday | tuesday | wednesday | thursday | friday | saturday | sunday

open day

definition next_weekday : day → day
| next_weekday monday    := tuesday
| next_weekday tuesday   := wednesday
| next_weekday wednesday := thursday
| next_weekday thursday  := friday
| next_weekday _         := monday

theorem next_weekday_monday    : next_weekday monday    = tuesday   := rfl
theorem next_weekday_tuesday   : next_weekday tuesday   = wednesday := rfl
theorem next_weekday_wednesday : next_weekday wednesday = thursday  := rfl
theorem next_weekday_thursday  : next_weekday thursday  = friday    := rfl
theorem next_weekday_friday    : next_weekday friday    = monday    := rfl
theorem next_weekday_sat       : next_weekday saturday  = monday    := rfl
theorem next_weekday_sunday    : next_weekday sunday    = monday    := rfl

example : next_weekday (next_weekday monday) = wednesday :=
rfl

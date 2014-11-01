import logic

inductive day :=
monday, tuesday, wednesday, thursday, friday, saturday, sunday

namespace day

  definition next_weekday d :=
  rec_on d tuesday wednesday thursday friday monday monday monday

  example test_next_weekday : next_weekday (next_weekday saturday) = tuesday :=
  rfl

end day

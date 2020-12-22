inductive Weekday where
  | sunday    : Weekday
  | monday    : Weekday
  | tuesday   : Weekday
  | wednesday : Weekday
  | thursday  : Weekday
  | friday    : Weekday
  | saturday  : Weekday

def Weekday.next : Weekday -> Weekday :=
  fun d => match d with
    | sunday    => monday
    | monday    => tuesday
    | tuesday   => wednesday
    | wednesday => thursday
    | thursday  => friday
    | friday    => saturday
    | saturday  => sunday

def Weekday.previous : Weekday -> Weekday
  | sunday    => saturday
  | monday    => sunday
  | tuesday   => monday
  | wednesday => tuesday
  | thursday  => wednesday
  | friday    => thursday
  | saturday  => friday

theorem Weekday.nextOfPrevious (d : Weekday) : next (previous d) = d := by
  cases d
  allGoals rfl

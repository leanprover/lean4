/-- info: 0 -/
#guard_msgs in
#eval Array.foldl (·+·) 0 #[1,2,3] (start := 5) (stop := 10)

/-- info: 0 -/
#guard_msgs in
#eval ByteArray.foldl (·+·) 0 ⟨#[1,2,3]⟩ (start := 5) (stop := 10)

/-- info: 0.000000 -/
#guard_msgs in
#eval FloatArray.foldl (·+·) 0 ⟨#[1,2,3]⟩ (start := 5) (stop := 10)

module

def s₁ : String := Id.run do
  let mut ans := ""
  for c in 'a'...='z' do
    ans := ans.push c
  return ans

/-- info: "abcdefghijklmnopqrstuvwxyz" -/
#guard_msgs in
#eval s₁

def s₂ : String := Id.run do
  let mut ans := ""
  for c in 'a'...'z' do
    ans := ans.push c
  return ans

/-- info: "abcdefghijklmnopqrstuvwxy" -/
#guard_msgs in
#eval s₂

/-- info: 122 -/
#guard_msgs in
#eval (*...'z').size

/-- info: 1112064 -/
#guard_msgs in
#eval (*...* : Std.Rii Char).size

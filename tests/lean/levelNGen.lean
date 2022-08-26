opaque test1 {α : Sort _} : α → Sort u_1
#check @test1
def test2 {α : Sort _} : α → Sort u_1 := sorry
#check @test2
variable {α : Sort _} in theorem test3 : α → Sort _ := sorry
#check @test3

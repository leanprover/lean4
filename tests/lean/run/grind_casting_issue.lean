
set_option grind.warning false
@[grind] def codelen (c: List Bool) : Int := c.length

theorem issue1 : codelen [] = 0 := by grind

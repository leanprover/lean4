#eval (1073741823:int)
#eval (1073741824:int)
#eval ((1073741824:int) + (1:int) - (3:int))
#eval - (2:int)
#eval - (1000:int)
#eval 10 - (1000:int)
#eval (1073741824:int) * 10
#eval (100000:int) * (-3:int)
#eval -(1073741823:int)
#eval ((1073741824:int) + (1:int) - (1:int))
#eval int.of_nat 1000
#eval int.of_nat 1073741823

def Abs : int → nat
| (int.of_nat n)          := n
| (int.neg_succ_of_nat n) := n + 1

#eval 10000
#eval Abs (- 10000)
#eval Abs (-1073741823)
#eval Abs (-1073741824)
#eval Abs (-1073741825)

#eval -(1073741823:int) * 1000000000

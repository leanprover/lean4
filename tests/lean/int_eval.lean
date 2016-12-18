vm_eval (1073741823:int)
vm_eval (1073741824:int)
vm_eval ((1073741824:int) + (1:int) - (3:int))
vm_eval - (2:int)
vm_eval - (1000:int)
vm_eval 10 - (1000:int)
vm_eval (1073741824:int) * 10
vm_eval (100000:int) * (-3:int)
vm_eval -(1073741823:int)
vm_eval ((1073741824:int) + (1:int) - (1:int))
vm_eval int.of_nat 1000
vm_eval int.of_nat 1073741823

def Abs : int → nat
| (int.of_nat n)          := n
| (int.neg_succ_of_nat n) := n + 1

vm_eval 10000
vm_eval Abs (- 10000)
vm_eval Abs (-1073741823)
vm_eval Abs (-1073741824)
vm_eval Abs (-1073741825)

vm_eval -(1073741823:int) * 1000000000

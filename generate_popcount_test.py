import os 

output_file = open('test_popcount_correctness.lean', 'w')

output_file.write('import Std.Tactic.BVDecide\n')

width = 9

for n in range(0, pow(2, width)):
    popcount_golden = n.bit_count()
    output_file.write("example {x : BitVec "+str(width)+"} (h : x = "+str(n)+"#"+str(width)+") : x.popCount = "+str(popcount_golden)+" := by bv_decide\n")

output_file.close()
def Int64Min : Int := -1*(Int.ofNat ((UInt64.size / 2)))

#eval   Int.negSucc 9223372036854775807
#reduce Int.negSucc 9223372036854775807
#print "---"
#eval   - Int.negSucc 9223372036854775807
#reduce - Int.negSucc 9223372036854775807
#print "---"
#eval   Int.negSucc 9223372036854775807 == 0
#reduce Int.negSucc 9223372036854775807 == 0
#print "---"
#eval   Int.negSucc 9223372036854775807 == Int64Min
#reduce Int.negSucc 9223372036854775807 == Int64Min
#print "---"
#eval   (Int.negSucc 9223372036854775807) + 1 == 1
#reduce (Int.negSucc 9223372036854775807) + 1 == 1

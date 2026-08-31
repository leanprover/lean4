
-- complement
#guard ~~~(-1:Int) = 0
#guard ~~~(0:Int) = -1
#guard ~~~(1:Int) = -2
#guard ~~~(-2:Int) = 1

-- shiftRight
#guard (2:Int) >>> 1 = 1
#guard (0:Int) >>> 1 = 0
#guard ~~~(1:Int) >>> 1 = ~~~0
#guard ~~~(0:Int) >>> 1 = ~~~0
#guard ~~~(2:Int) >>> 1 = ~~~1
#guard ~~~(4:Int) >>> 1 = ~~~2
#guard ~~~(4:Int) >>> 2 = ~~~1

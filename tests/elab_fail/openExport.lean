

def A.x := 10

namespace B

export A (x)

def y := 20

#check x -- works
#check y -- works

end B

#check A.x -- works
#check B.x -- works, but fails in old frontend and Lean3 :)
#check B.y -- works
#check x -- fails as expected
#check y -- fails as expected
open B
#check x -- works
#check y -- works

namespace B

#check x -- works
#check y -- works

def z := 30

#check z -- works
end B

#check z  -- works, but fails in old frontend and Lean3 :)

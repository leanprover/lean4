structure UInt128 where
  lo : UInt64
  hi : UInt64

def zero : UInt128 := ⟨0, 0⟩

@[noinline]
def compl (n : UInt64) : UInt64 := n.complement

def exp : UInt64 := compl <| compl <| compl zero.hi

#eval exp

abbrev UnsignedInt64 := UInt64

structure UnsignedInt128 where
  hi : UnsignedInt64
  lo : UnsignedInt64

def zero' : UnsignedInt128 := ⟨0, 0⟩

@[noinline]
def compl' (n : UnsignedInt64) : UnsignedInt64 := n.complement

def exp' : UnsignedInt64 := compl' <| compl' <| compl' zero'.hi

#eval exp'

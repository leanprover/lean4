import Dep.Basic

@[export my_length]
def myLength (s : String) : UInt64 :=
  s.length.toUInt64 + magicNumber.toUInt64

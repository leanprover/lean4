scoped instance : ToString Bool where -- Error
  toString b := if b then "t" else "f"

#eval toString true

scoped infix:65 "+" => Nat.add -- Error

set_option warn.classDefReducibility false in
@[scoped instance] -- Error
def myInst : ToString Bool where
  toString b := if b then "t" else "f"

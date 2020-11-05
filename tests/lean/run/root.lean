def x := 10


namespace Foo

def x := true

#check x
#check _root_.x

theorem ex1 : x = true := rfl
theorem ex2 : _root_.x = 10 := rfl

end Foo

theorem ex3 : x = 10 := rfl
theorem ex4 : _root_.x = 10 := rfl

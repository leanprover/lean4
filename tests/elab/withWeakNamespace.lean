/-
Tests for `with_weak_namespace` command
-/

-- Test 1: Basic absolute namespace usage
namespace Foo

def f : Nat := 1

scoped infix:65 " + " => f

with_weak_namespace _root_.Bar
  def g : Nat := 2
  #check 1 + 2  -- Scoped notation still works
  #check Bar.g

end Foo

#check Bar.g
#check Foo.f

-- Test 2: _root_ handling
namespace A.B

with_weak_namespace _root_.C
  def x : Nat := 1

end A.B

#check C.x

-- Test 3: Scoped notation persists
namespace Outer

def outerDef : Nat := 5

scoped infix:70 " * " => outerDef

with_weak_namespace _root_.Test1
  #check 1 * 2  -- Scoped notation from Outer still works

end Outer

-- Test 4: Relative namespace (without _root_)
namespace Parent

def parentFn (n : Nat) : Nat := n + 10

scoped prefix:100 "!" => parentFn

with_weak_namespace Child
  def childDef : Nat := !0  -- Scoped notation from Parent still works
  #check Parent.Child.childDef

end Parent

#check Parent.Child.childDef

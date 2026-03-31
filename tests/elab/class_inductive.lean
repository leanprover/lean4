namespace Foo

def A (α : Type) := α × α

end Foo

class inductive Foo.Bar (α : Type) where
  | mk₁ (a : A α)
  | mk₂ (a : A α)

#check @Foo.Bar.mk₁
#check @Foo.Bar.mk₂

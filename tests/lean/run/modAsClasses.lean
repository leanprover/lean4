class MyMod :=
(a : Nat)

namespace MyMod
variable [MyMod]
def b := a + 1
end MyMod

def myMod1 : MyMod := ⟨0⟩

#eval myMod1.a
#eval myMod1.b

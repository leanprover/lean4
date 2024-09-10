class MyMod :=
(a : Nat)

namespace MyMod
variable [MyMod]
def b := a + 1
end MyMod

def myMod1 : MyMod := ⟨0⟩

#guard myMod1.a == 0
#guard myMod1.b == 1

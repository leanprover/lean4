namespace Ex1
  class FunLike (F : Sort _) (β : outParam <| Nat → Sort _) where
    coe : F → ∀ a, β a

  inductive Secret
  def Wrapper := Secret
  inductive Bla | z
  instance : FunLike Bla (fun _ => Wrapper) := sorry

  instance (priority := 100) {F β} [FunLike F β] :
    CoeFun F fun _ => ∀ a : Nat, β a where coe := FunLike.coe

  #check Bla.z ∘ id
end Ex1


namespace Ex2
structure Secret
def Wrapper := Secret
def f (a : Nat) : (fun _ => Wrapper) a := ⟨⟩

#check f ∘ id
end Ex2

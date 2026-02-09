class L0  where f : Type _
class A0  where a : Type _
class B0  where b : Type _
instance [A0] [B0] : L0 := ⟨A0.a × B0.b⟩
class A1
instance [A1] : A0 := ⟨Nat⟩
class L1 extends A1, B0
class C0 [L0]
-- instance [L1] : L0 := inferInstance
instance [L1] : C0 := ⟨⟩

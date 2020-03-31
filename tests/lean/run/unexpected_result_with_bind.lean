namespace Repro

def FooM (α : Type) : Type := Unit → α
def FooM.run {α : Type} (ψ : FooM α) (x : Unit) : α := ψ x

def bind {α β : Type} : ∀ (ψ₁ : FooM α) (ψ₂ : α → FooM β), FooM β
| ψ₁, ψ₂ => λ _ => ψ₂ (ψ₁.run ()) ()

instance : HasPure FooM := ⟨λ _ x => λ _ => x⟩
instance : HasBind FooM := ⟨@bind⟩
instance : Monad FooM := {}

def unexpectedBehavior : FooM String := do
let b : Bool := (#[] : Array Nat).isEmpty;
trueBranch  ← pure "trueBranch";
falseBranch ← pure "falseBranch";
(1 : Nat).foldM (λ _ (s : String) => do
  s ← pure $ if b then trueBranch else falseBranch; pure s) ""

#eval unexpectedBehavior () --#["falseBranch"]

end Repro

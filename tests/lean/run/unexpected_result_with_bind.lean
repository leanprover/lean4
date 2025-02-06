
namespace Repro

def FooM (α : Type) : Type := Unit → α
def FooM.run {α : Type} (ψ : FooM α) (x : Unit) : α := ψ x

def bind {α β : Type} : ∀ (ψ₁ : FooM α) (ψ₂ : α → FooM β), FooM β
| ψ₁, ψ₂ => λ _ => ψ₂ (ψ₁.run ()) ()

instance : Pure FooM := ⟨λ x => λ _ => x⟩
instance : Bind FooM := ⟨@bind⟩
instance : Monad FooM := {}

def unexpectedBehavior : FooM String := do
let b : Bool := (#[] : Array Nat).isEmpty;
let trueBranch  ← pure "trueBranch";
let falseBranch ← pure "falseBranch";
(1 : Nat).foldM (λ _ _ (s : String) => do
  let s ← pure $ if b then trueBranch else falseBranch; pure s) ""

/-- info: "trueBranch" -/
#guard_msgs in
#eval unexpectedBehavior ()

end Repro

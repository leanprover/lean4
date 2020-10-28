/-
Same setup as in 'equation_compiler_slow_with_many_constructors.lean',
except here we have a function `infer` that takes a single `Proof` object
and that matches on all constructors, each applied only to variables.
Despite the favorable matching regime, the function `infer` still takes ~200ms
to elaborate.
-/
namespace ECSlow

inductive Op : Type
| add, mul

namespace Op

def hasToString : Op → String
| add => "add"
| mul => "mul"

instance : ToString Op := ⟨hasToString⟩

def beq : Op → Op → Bool
| add, add => true
| mul, mul => true
| _,   _   => false

instance : BEq Op := ⟨beq⟩

end Op

open Op

inductive Term : Type
| ofInt  : Int → Term
| var    : Nat → Term
| varPow : Nat → Nat → Term
| app    : Op → Term → Term → Term

namespace Term

def beq : Term → Term → Bool
| ofInt n₁,      ofInt n₂      => n₁ == n₂
| var v₁,        var v₂        => v₁ == v₂
| varPow v₁ k₁,  varPow v₂ k₂  => v₁ == v₂ && k₁ == k₂
| app op₁ x₁ y₁, app op₂ x₂ y₂ => op₁ == op₂ && beq x₁ x₂ && beq y₁ y₂
| _,             _             => false

instance : BEq Term := ⟨beq⟩

instance : HasZero Term := ⟨ofInt 0⟩
instance : HasOne Term := ⟨ofInt 1⟩
instance : Add Term := ⟨app add⟩
instance : Mul Term := ⟨app mul⟩
instance : Neg Term := ⟨app mul (ofInt (-1))⟩
instance : Sub Term := ⟨λ x y => app add x (- y)⟩

end Term

open Term

inductive Proof : Type
| addZero   : Term → Proof
| zeroAdd   : Term → Proof
| addComm   : Term → Term → Proof
| addCommL  : Term → Term → Term → Proof
| addAssoc  : Term → Term → Term → Proof
| mulZero   : Term → Proof
| zeroMul   : Term → Proof
| mulOne    : Term → Proof
| oneMul    : Term → Proof
| mulComm   : Term → Term → Proof
| mulCommL  : Term → Term → Term → Proof
| mulAssoc  : Term → Term → Term → Proof
| distribL  : Term → Term → Term → Proof
| distribR  : Term → Term → Term → Proof
| ofIntAdd  : Int → Int → Proof
| ofIntMul  : Int → Int → Proof
| powZero   : Nat → Proof
| powOne    : Nat → Proof
| powMerge  : Nat → Nat → Nat → Proof
| powMergeL : Nat → Nat → Nat → Term → Proof
| congrArg₁ : Op → Proof → Term → Proof
| congrArg₂ : Op → Term → Proof → Proof
| congrArgs : Op → Proof → Proof → Proof
| refl      : Term → Proof
| trans     : Proof → Proof → Proof

namespace Proof

/-
[Leo] elaboration time is now at 50ms on my machine.
The problem was not the equation compiler, but time wasted trying
to synthesize `[MonadFail Except]`.

We used to have the instances
```
instance monadFailLift (m n : Type u → Type v) [HasMonadLift m n] [MonadFail m] [Monad n] : MonadFail n :=
{ fail := fun α s => monadLift (MonadFail.fail s : m α) }
instance I1 (m : Type → Type) [Monad m] : MonadFail (ExceptT String m)
```
The instance `monadFailLift` triggers the performance problem when trying to solve `[MonadFail (Except String)]`.
It produces the subgoals
```
[MonadFail ?m]
[HasMonadLift ?m (Except String)]
```
Then we try to solve `[MonadFail ?m]` using `I1` we can produces an infinite number of solutions.
The first solution is `?m := ExceptT String (EIO ?ε)` where `EIO ?ε` is the first Monad Lean managed to synthesize when solving I1.
Then it uses the instance
```lean
instance (m : Type → Type) [Monad m] : Monad (OptionT m) :=
```
to generate the solutions
```
?m := ExceptT String (OptionT (EIO ?ε))
?m := ExceptT String (OptionT $ OptionT (EIO ?ε))
?m := ExceptT String (OptionT $ OptionT $ OptionT (EIO ?ε))
...
```
Note that the new type class resolution procedure would not solve this problem. If we wanted to keep this feature, the solution would be to write
```
instance monadFailLift (m n : Type u → Type v) [HasMonadLift m n] [MonadFail m] [Monad n] : MonadFail n :=
```
as
```
instance monadFailLift (m n : Type u → Type v) [MonadFail m] [HasMonadLift m n] [Monad n] : MonadFail n :=
```
The subgoal `[HasMonadLift ?m (Except String)]` would fail instantaneously.
-/

def infer : Proof → Except String (Term × Term)
| addZero x => pure (x+0, x)
| zeroAdd y => pure (0 + y, y)
| addComm x y => pure (x + y, y + x)
| addCommL x y z => pure (x + (y + z), y + (x + z))
| addAssoc x y z => pure ((x + y) + z, x + (y + z))
| mulZero x => pure (x * 0, 0)
| zeroMul y => pure (0 * y, 0)
| mulOne x => pure (x * 1, x)
| oneMul y => pure (1 * y, y)
| mulComm x y => pure (x * y, y * x)
| mulCommL x y z => pure (x * (y * z), y * (x * z))
| mulAssoc x y z => pure ((x * y) * z, x * (y * z))
| distribL x y z => pure (x * (y + z), x * y + x * z)
| distribR x y z => pure ((x + y) * z, x * z + y * z)
| ofIntAdd m n => pure (ofInt m + ofInt n, ofInt $ m + n)
| ofIntMul m n => pure (ofInt m * ofInt n, ofInt $ m * n)
| powZero v => pure (varPow v 0, 1)
| powOne v => pure (var v, varPow v 1)
| powMerge v m n => pure (varPow v m * varPow v n, varPow v (m+n))
| powMergeL v m n t => pure (varPow v m * (varPow v n * t), varPow v (m+n) * t)
| congrArg₁ op px y => do (x₁, x₂) ← infer px; pure (app op x₁ y, app op x₂ y)
| congrArg₂ op x py => do (y₁, y₂) ← infer py; pure (app op x y₁, app op x y₂)
| congrArgs op px py => do (x₁, x₂) ← infer px; (y₁, y₂) ← infer py; pure (app op x₁ y₁, app op x₂ y₂)
| refl t => pure (t, t)
| trans p₁ p₂ => do
  (x, y₁) ← infer p₁;
  (y₂, z) ← infer p₂;
  if y₁ == y₂ then pure (x, z) else throw "invalid proof"

end Proof
end ECSlow

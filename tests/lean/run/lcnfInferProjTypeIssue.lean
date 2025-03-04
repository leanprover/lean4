import Lean

structure Vec2 where
  (x y : Float)

instance : Add Vec2 :=
  ⟨λ ⟨x₁,x₂⟩ ⟨y₁, y₂⟩ => ⟨x₁+y₁, x₂+y₂⟩⟩

instance : HMul Float Vec2 Vec2 :=
  ⟨λ s ⟨x₁,x₂⟩ => ⟨s*x₁, s*x₂⟩⟩

def NFloatArray (n : Nat) := {a : FloatArray // a.size = n}

instance {n} : Add (NFloatArray n) :=
 ⟨λ x y => Id.run do
   let mut x := x.1
   for i in [0:n] do
     x := x.set i (x[i]'sorry+y.1[i]'sorry) sorry
   ⟨x,sorry⟩⟩

instance {n} : HMul Float (NFloatArray n) (NFloatArray n) :=
 ⟨λ s x => Id.run do
   let mut x := x.1
   for i in [0:n] do
     x := x.set i (s*x[i]'sorry) sorry
   ⟨x,sorry⟩⟩

def FloatVector : Nat → Type
  | 0 => Unit
  | 1 => Float
  | 2 => Vec2
  | (n+3) => NFloatArray (n+3)

@[inline] def FloatVector.add {n : Nat} (x y : FloatVector n) : FloatVector n :=
  match n with
  | 0 => Unit.unit
  | 1 =>     by unfold FloatVector at x y; apply x + y
  | 2 =>     by unfold FloatVector at x y; apply x + y
  | (_+3) => by unfold FloatVector at x y; apply x + y

def FloatVector.smul {n : Nat} (s : Float) (x : FloatVector n) : FloatVector n :=
  match n with
  | 0 => Unit.unit
  | 1 =>     by unfold FloatVector at x; apply s*x
  | 2 =>     by unfold FloatVector at x; apply s*x
  | (_+3) => by unfold FloatVector at x; apply s*x


instance : Add (FloatVector n) := ⟨λ x y => x.add y⟩
instance : HMul Float (FloatVector n) (FloatVector n) := ⟨λ s x => x.smul s⟩

def foo1 := λ (x y : FloatVector 2) => x + y

def foo2 := λ {n} (s : Float) (x y : FloatVector n) => s * (x + y)

run_meta Lean.Compiler.compile #[``foo1]
run_meta Lean.Compiler.compile #[``foo2]

set_option trace.Compiler.result true
set_option pp.funBinderTypes true
run_meta Lean.Compiler.compile #[``foo1]
run_meta Lean.Compiler.compile #[``foo2]

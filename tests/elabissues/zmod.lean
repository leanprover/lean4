class Fact (p : Prop) :=
(h : p)

class Ring (α : Type) :=
(one : α) -- dummy implementation

instance ringHasOne {α} [Ring α] : HasOne α :=
⟨Ring.one α⟩ -- dummy implementation

instance ringAdd {α} [Ring α] : Add α :=
⟨fun a b => a⟩ -- dummy implementation

instance ringMul {α} [Ring α] : Mul α :=
⟨fun a b => a⟩ -- dummy implementation

class Field (α : Type) extends Ring α :=
(otherStuff : Unit := ()) -- dummy implementation

instance fieldDiv {α} [Field α] : Div α :=
⟨fun a b => a⟩ -- dummy implementation

def IsPrime (n : Nat) : Prop :=
True  -- dummy implementation

structure Zmod (n : Nat) :=
(dummy : Unit := ()) -- dummy implementation

instance zmodIsRing {n : Nat} : Ring (Zmod n) :=
{ one := {} }

/- After the instance above, Zmod already has `+`, `*` notations, but not `/`  -/

set_option pp.explicit true
set_option pp.notation false

#check fun (a b : Zmod 10) => a * b -- works

#check fun (a b : Zmod 10) => a / b -- fails

instance zmodIsField {n : Nat} [Fact (IsPrime n)] : Field (Zmod n) :=
{}

#check fun (a b : Zmod 3) => a / b -- fails because local instance [Fact (IsPrime 3)] is not available

#check fun (a b : Zmod 3) (h : Fact (IsPrime 3)) => a / b -- works

axiom foo {n : Nat} (h : Fact (IsPrime n)) (a : Zmod n) : a / a = 1 -- We need hypothesis `h` to be able to write `a/a`

#check fun {n : Nat} (h : IsPrime n) (a : Zmod n) => foo ⟨h⟩ a -- need to use ⟨...⟩ to convert `IsPrime n` into `Fact (IsPrime n)`

-- We can add a coercion from `p` to `Fact p` to minimize the amount of manual wrapping
instance toFact (p : Prop) : HasCoeT p (Fact p) :=
⟨fun h => ⟨h⟩⟩

#check fun {n : Nat} (h : IsPrime n) (a : Zmod n) => @foo n h a -- coercion helps. I needed to use `@` due to a Lean3 issue that is being fixed in Lean4

/- We support cycles in the new TC. So, we can also define -/
instance ofFact (p : Prop) : HasCoeT (Fact p) p :=
⟨fun h => h.1⟩

/- So, the coercions make it easy to wrap/unwrap facts -/

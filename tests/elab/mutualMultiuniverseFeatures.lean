/-!
# `mutual_multiuniverse`: parameters, indices, choice, and the degenerate cases
-/

/-! ## Parameters -/

mutual_multiuniverse
inductive Wrap (α : Type) : Prop where
  | mk : Box α → Wrap α
inductive Box (α : Type) : Type 1 where
  | val : α → Type → Box α
  | back : Wrap α → Box α
end

/-- info: 'Wrap.rec' does not depend on any axioms -/
#guard_msgs in
#print axioms Wrap.rec

example (α : Type) (b : Box α) : Wrap α := Wrap.mk b

def boxTag {α : Type} : Box α → Nat
  | .val _ _ => 0
  | .back _ => 1

/-- info: 1 -/
#guard_msgs in
#eval boxTag (Box.back (Wrap.mk (Box.val 3 Nat)))

/-! ## Indices, with the data member carrying data

`Ev n` says `n` is even; `Od n` is a *datum* attached to an odd `n`.  The two
are genuinely mutually recursive and genuinely at different universes. -/

mutual_multiuniverse
inductive Ev : Nat → Prop where
  | zero : Ev 0
  | succ : (n : Nat) → Od n → Ev (n + 1)
inductive Od : Nat → Type 0 where
  | succ : (n : Nat) → Ev n → Nat → Od (n + 1)
end

/-- info: 'Od.mutualRec' does not depend on any axioms -/
#guard_msgs in
#print axioms Od.mutualRec

def three : Od 3 := Od.succ 2 (Ev.succ 1 (Od.succ 0 Ev.zero 7)) 9

def payload : {n : Nat} → Od n → Nat
  | _, .succ _ _ k => k

/-- info: 9 -/
#guard_msgs in
#eval payload three

-- iota for the indexed data member
example (n : Nat) (e : Ev n) (k : Nat)
    {mE : (n : Nat) → Ev n → Prop} {mO : (n : Nat) → Od n → Sort u}
    (cz : mE 0 Ev.zero)
    (cs : (n : Nat) → (o : Od n) → mO n o → mE (n + 1) (Ev.succ n o))
    (co : (n : Nat) → (e : Ev n) → (k : Nat) → mE n e → mO (n + 1) (Od.succ n e k)) :
    @Od.mutualRec mE mO cz cs co (n + 1) (Od.succ n e k)
      = co n e k (@Ev.mutualRec mE mO cz cs co n e) := rfl

/-! ## A function *into* a data member

This is the one shape that needs a choice principle: to recurse into a
`Nat → Stream'` field from a `Prop`, the witnesses have to be selected
pointwise. -/

mutual_multiuniverse
inductive Total : Prop where
  | mk : (Nat → Stream') → Total
inductive Stream' : Type 1 where
  | cons : Type → Stream' → Stream'
  | nil : Stream'
  | fromTotal : Total → Stream'
end

/-- info: 'Total.rec' depends on axioms: [Classical.choice] -/
#guard_msgs in
#print axioms Total.rec

-- and `Stream'.mutualRec` inherits it, since the induction hypothesis for
-- `Stream'.fromTotal`'s field *is* `Total.mutualRec`
/-- info: 'Stream'.mutualRec' depends on axioms: [Classical.choice] -/
#guard_msgs in
#print axioms Stream'.mutualRec

-- the native recursor is unaffected: it does not recurse into `Total` at all
/-- info: 'Stream'.rec' does not depend on any axioms -/
#guard_msgs in
#print axioms Stream'.rec

/-! ## No `Prop` member at all

Two data members at different universes, with only one direction of dependency
("unnecessarily mutual").  No shadow is built and no choice is needed. -/

mutual_multiuniverse
inductive Low : Type 0 where
  | z : Low
  | s : Low → Low
inductive High : Type 3 where
  | mk : Low → Type 2 → High
  | nest : High → High
end

/-- info: 'High.mutualRec' does not depend on any axioms -/
#guard_msgs in
#print axioms High.mutualRec

def lowSize : Low → Nat
  | .z => 0
  | .s l => lowSize l + 1

/-- info: 2 -/
#guard_msgs in
#eval lowSize (Low.s (Low.s Low.z))

example (l : Low) (t : Type 2)
    {mL : Low → Sort u} {mH : High → Sort v}
    (cz : mL Low.z) (cs : (l : Low) → mL l → mL l.s)
    (cm : (l : Low) → (t : Type 2) → mL l → mH (High.mk l t))
    (cn : (h : High) → mH h → mH h.nest) :
    @High.mutualRec mL mH cz cs cm cn (High.mk l t)
      = cm l t (@Low.mutualRec mL mH cz cs cm cn l) := rfl

/-! ## Section variables and `deriving`

A section `variable` used by any member becomes a parameter of the whole block,
exactly as under `mutual`.  A member's free variable stands for the member
*already applied* to those variables, so the lowering substitutes for it under
the parameter telescope. -/

section
variable (α : Type)

mutual_multiuniverse
inductive SWrap : Prop where
  | mk : SBox → SWrap
inductive SBox : Type 1 where
  | val : α → Type → SBox
  | back : SWrap → SBox
end

end

/-- info: SWrap : Type → Prop -/
#guard_msgs in
#check @SWrap

/-- info: @SBox.val : {α : Type} → α → Type → SBox α -/
#guard_msgs in
#check @SBox.val

/--
info: @SWrap.mutualRec : ∀ {α : Type} {motive_1 : SWrap α → Prop} {motive_2 : SBox α → Sort u_1},
  (∀ (a : SBox α) (ih_1 : motive_2 a), motive_1 (SWrap.mk a)) →
    ∀ (case_2 : (a : α) → (a_1 : Type) → motive_2 (SBox.val a a_1))
      (case_3 : (a : SWrap α) → motive_1 a → motive_2 (SBox.back a)) (t : SWrap α), motive_1 t
-/
#guard_msgs in
set_option pp.proofs true in
#check @SWrap.mutualRec

/-- info: 'SWrap.mutualRec' does not depend on any axioms -/
#guard_msgs in
#print axioms SWrap.mutualRec

def sTag {α : Type} : SBox α → Nat
  | .val _ _ => 0
  | .back _ => 1

/-- info: 1 -/
#guard_msgs in
#eval sTag (SBox.back (SWrap.mk (SBox.val (3 : Nat) Nat)))

-- a `deriving` clause on a data member is honoured, since the data members are
-- ordinary inductive types by the time the handlers run
mutual_multiuniverse
inductive DP : Prop where
  | mk : DD → DP
inductive DD : Type 1 where
  | z
  | s : DD → DD
  deriving Repr
end

/-- info: DD.s (DD.z) -/
#guard_msgs in
#eval repr (DD.s DD.z)

/-! ## A genuine cycle among the data members

`GX` and `GY` are mutually recursive at the same universe, so they form one
strongly connected component and are declared as a single ordinary `mutual`
block; `GZ` depends on both and forms a later one.  A member's native `X.rec`
ranges over its own component, so `GX.rec` has two motives and `GZ.rec` has
one. -/

mutual_multiuniverse
inductive GP : Prop where
  | fromX : GX → GP
  | fromY : GY → GP
inductive GX : Type 0 where
  | mk : GY → GX
  | leaf : Nat → GX
inductive GY : Type 0 where
  | mk : GX → GY
  | fromP : GP → GY
inductive GZ : Type 2 where
  | mk : GX → GY → Type 1 → GZ
end

/--
info: @GX.rec : {motive_1 : GX → Sort u_1} →
  {motive_2 : GY → Sort u_1} →
    ((a : GY) → motive_2 a → motive_1 (GX.mk a)) →
      ((a : Nat) → motive_1 (GX.leaf a)) →
        ((a : GX) → motive_1 a → motive_2 (GY.mk a)) → ((a : GP) → motive_2 (GY.fromP a)) → (t : GX) → motive_1 t
-/
#guard_msgs in
#check @GX.rec

/--
info: @GZ.rec : {motive : GZ → Sort u_1} →
  ((a : GX) → (a_1 : GY) → (a_2 : Type 1) → motive (GZ.mk a a_1 a_2)) → (t : GZ) → motive t
-/
#guard_msgs in
#check @GZ.rec

/-- info: 'GP.mutualRec' does not depend on any axioms -/
#guard_msgs in
#print axioms GP.mutualRec

/-- info: 'GZ.mutualRec' does not depend on any axioms -/
#guard_msgs in
#print axioms GZ.mutualRec

-- structural recursion works across the component
mutual
def gxSize : GX → Nat
  | .mk y => gySize y + 1
  | .leaf n => n
def gySize : GY → Nat
  | .mk x => gxSize x + 1
  | .fromP _ => 0
end

/-- info: 7 -/
#guard_msgs in
#eval gxSize (GX.mk (GY.mk (GX.leaf 5)))

/-! ## Universe polymorphism -/

mutual_multiuniverse
inductive UP (α : Type u) : Prop where
  | mk : UD α → UP α
inductive UD (α : Type u) : Type (u + 1) where
  | val : α → Type u → UD α
  | back : UP α → UD α
end

/-- info: UD : Type u_1 → Type (u_1 + 1) -/
#guard_msgs in
#check @UD

/--
info: @UD.mutualRec : {α : Type u_2} →
  {motive_1 : UP α → Prop} →
    {motive_2 : UD α → Sort u_1} →
      (∀ (a : UD α) (ih_1 : motive_2 a), motive_1 (UP.mk a)) →
        ((a : α) → (a_1 : Type u_2) → motive_2 (UD.val a a_1)) →
          ((a : UP α) → motive_1 a → motive_2 (UD.back a)) → (t : UD α) → motive_2 t
-/
#guard_msgs in
set_option pp.proofs true in
#check @UD.mutualRec

/-- info: 'UD.mutualRec' does not depend on any axioms -/
#guard_msgs in
#print axioms UD.mutualRec

def uTag {α : Type u} : UD α → Nat
  | .val _ _ => 0
  | .back _ => 1

/-- info: 0 -/
#guard_msgs in
#eval uTag (UD.val (3 : Nat) Nat)

/-! ## A homogeneous block is an ordinary `mutual` block

`mutual_multiuniverse` accepts everything `mutual` does and means the same
thing by it; the block below is emitted natively and `mutualRec` is just
another name for the native recursor. -/

mutual_multiuniverse
inductive T1 : Type where
  | mk : T2 → T1
inductive T2 : Type where
  | mk : T1 → T2
  | stop : T2
end

example : @T1.mutualRec = @T1.rec := rfl

/-- info: 'T1.rec' does not depend on any axioms -/
#guard_msgs in
#print axioms T1.rec

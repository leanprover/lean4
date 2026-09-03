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

-- the same thing through the block-wide recursor, which is computable too
def boxTag' {α : Type} : Box α → Nat :=
  @Box.mutualRec α (fun _ => True) (fun _ => Nat)
    (fun _ _ => trivial) (fun _ _ => 0) (fun _ _ => 1)

/-- info: 1 -/
#guard_msgs in
#eval boxTag' (Box.back (Wrap.mk (Box.val 3 Nat)))

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

-- and it is computable, indices and all.  Only one level of payload is
-- reachable: the recursion into `Od` goes through `Ev`, whose motive is a
-- `Prop`, so there is nothing to accumulate -- which is the whole point.
def odPayload : (n : Nat) → Od n → Nat :=
  @Od.mutualRec (fun _ _ => True) (fun _ _ => Nat)
    trivial (fun _ _ _ => trivial) (fun _ _ k _ => k)

example : odPayload 3 three = 9 := rfl

/-- info: 9 -/
#guard_msgs in
#eval odPayload 3 three

/-! ## A function *into* a data member

This is the one shape that needs a choice principle: to recurse into a
`Nat → Stream'` field from a `Prop`, the witnesses have to be selected
pointwise.  It is the field's type that matters, not which member carries it --
a `Prop` member's recursor goes through the shadow of the whole block, so an
infinitary field on a *data* member does it too. -/

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

-- depending on `Classical.choice` and being computable are not in conflict
-- here: the choice happens under a `Prop`, so it has no computational content
-- and the compiled code never reaches it
def sLen : Stream' → Nat :=
  @Stream'.mutualRec (fun _ => True) (fun _ => Nat)
    (fun _ _ => trivial) (fun _ _ ih => ih + 1) 0 (fun _ _ => 0)

example : sLen (Stream'.cons Nat (Stream'.cons Bool Stream'.nil)) = 2 := rfl

/-- info: 2 -/
#guard_msgs in
#eval sLen (Stream'.cons Nat (Stream'.cons Bool Stream'.nil))

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

-- so does the block-wide recursor, both within the component and across it
def gxDepth : GX → Nat :=
  @GX.mutualRec (fun _ => True) (fun _ => Nat) (fun _ => Nat) (fun _ => Nat)
    (fun _ _ => trivial) (fun _ _ => trivial)
    (fun _ ih => ih + 1) (fun n => n)
    (fun _ ih => ih + 1) (fun _ _ => 0)
    (fun _ _ _ ihx ihy => ihx + ihy)

def gzSize : GZ → Nat :=
  @GZ.mutualRec (fun _ => True) (fun _ => Nat) (fun _ => Nat) (fun _ => Nat)
    (fun _ _ => trivial) (fun _ _ => trivial)
    (fun _ ih => ih + 1) (fun n => n)
    (fun _ ih => ih + 1) (fun _ _ => 0)
    (fun _ _ _ ihx ihy => ihx + ihy)

example : gxDepth (GX.mk (GY.mk (GX.leaf 5))) = 7 := rfl

/-- info: 7 -/
#guard_msgs in
#eval gxDepth (GX.mk (GY.mk (GX.leaf 5)))

/-- info: 7 -/
#guard_msgs in
#eval gzSize (GZ.mk (GX.mk (GY.mk (GX.leaf 5))) (GY.fromP (GP.fromX (GX.leaf 2))) (Type 0))

/-! ## Universe polymorphism -/

/-! ### A parameter and its universe -/

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

def uTag' {α : Type u} : UD α → Nat :=
  @UD.mutualRec α (fun _ => True) (fun _ => Nat)
    (fun _ _ => trivial) (fun _ _ => 0) (fun _ _ => 1)

/-- info: 1 -/
#guard_msgs in
#eval uTag' (UD.back (UP.mk (UD.val (3 : Nat) Nat)))

section
universe u v w

/-! ### Three universes at once

`Prop`, `Type u` and `Type (u + 1)`, all mutually referring to each other. The
universes have to be declared up front: with auto-bound implicits each member
gets its own level parameter, and a block whose members disagree about their
level parameters is rejected before we ever see it. -/

mutual_multiuniverse
inductive PA : Prop where
  | fromB : PB → PA
  | fromC : PC → PA
inductive PB : Type u where
  | leaf : Nat → PB
  | fromA : PA → PB
  | wrap : PB → PB
inductive PC : Type (u + 1) where
  | fromA : PA → PC
  | higher : Type u → PC
  | pair : PB → PC → PC
end

/-- info: PC.{u} : Type (u + 1) -/
#guard_msgs in
#check PC

section
variable {mA : PA.{u} → Prop} {mB : PB.{u} → Sort w} {mC : PC.{u} → Sort v}
  (fAB : (b : PB) → mB b → mA (PA.fromB b))
  (fAC : (c : PC) → mC c → mA (PA.fromC c))
  (fBl : (n : Nat) → mB (PB.leaf n))
  (fBa : (a : PA) → mA a → mB (PB.fromA a))
  (fBw : (b : PB) → mB b → mB (PB.wrap b))
  (fCa : (a : PA) → mA a → mC (PC.fromA a))
  (fCh : (t : Type u) → mC (PC.higher t))
  (fCp : (b : PB) → (c : PC) → mB b → mC c → mC (PC.pair b c))

-- the iota rule holds at a *variable* universe, not just at instantiations of it
example (b : PB.{u}) (c : PC.{u}) :
    @PC.mutualRec mA mB mC fAB fAC fBl fBa fBw fCa fCh fCp (PC.pair b c)
      = fCp b c (@PB.mutualRec mA mB mC fAB fAC fBl fBa fBw fCa fCh fCp b)
               (@PC.mutualRec mA mB mC fAB fAC fBl fBa fBw fCa fCh fCp c) := rfl
end

def cDepth : PC.{u} → Nat :=
  @PC.mutualRec (fun _ => True) (fun _ => Nat) (fun _ => Nat)
    (fun _ _ => trivial) (fun _ _ => trivial)
    (fun n => n) (fun _ _ => 0) (fun _ ih => ih + 1)
    (fun _ _ => 0) (fun _ => 0) (fun _ _ ihb ihc => ihb + ihc)

-- a universe-polymorphic definition has to be instantiated to be evaluated
/-- info: 5 -/
#guard_msgs in
#eval cDepth.{0} (PC.pair (PB.wrap (PB.leaf 4)) (PC.fromA (PA.fromB (PB.leaf 3))))

/-- info: 5 -/
#guard_msgs in
#eval cDepth.{3} (PC.pair (PB.wrap (PB.leaf 4)) (PC.fromA (PA.fromB (PB.leaf 3))))

/-- info: 'cDepth' does not depend on any axioms -/
#guard_msgs in
#print axioms cDepth

/-! ### The `csimp` pair is polymorphic too

`isConstantReplacement?` insists that the two sides of the equation be bare
constants with the same level parameters, so the theorem is stated about the
whole polymorphic family rather than an instantiation of it. -/

/-- info: PB.mutualRec.eq_impl : @PB.mutualRec = @PB.mutualRec.impl -/
#guard_msgs in
#check @PB.mutualRec.eq_impl

/-- info: 'PB.mutualRec.impl' does not depend on any axioms -/
#guard_msgs in
#print axioms PB.mutualRec.impl

/-! ### `imax` in a field

A dependent function `(a : α) → P a` lives at `Sort (imax (u+1) v)`, which is
`Prop` when `v` is. That is fine here: it is the *member's* universe that has to
be decidably `Prop`-or-not, and `IB` is declared at `Type (max u v)`. A member
declared at `Sort (imax u v)` is rejected -- see `mutualMultiuniverseErrors`. -/

mutual_multiuniverse
inductive IA (α : Type u) (P : α → Sort v) : Prop where
  | mk : IB α P → IA α P
inductive IB (α : Type u) (P : α → Sort v) : Type (max u v) where
  | fn : ((a : α) → P a) → IB α P
  | back : IA α P → IB α P
  | tag : Nat → IB α P
end

/-- info: IB.{u, v} (α : Type u) (P : α → Sort v) : Type (max u v) -/
#guard_msgs in
#check IB

def iTag {α : Type u} {P : α → Sort v} : IB α P → Nat :=
  @IB.mutualRec α P (fun _ => True) (fun _ => Nat)
    (fun _ _ => trivial) (fun _ => 0) (fun _ _ => 1) (fun n => n)

/-- info: 7 -/
#guard_msgs in
#eval iTag.{0, 0} (α := Nat) (P := fun _ => True) (IB.tag 7)

-- the dependent-function constructor, at a `Prop`-valued `P`, so the `imax`
-- collapses to `0` and the field is erased
/-- info: 0 -/
#guard_msgs in
#eval iTag.{0, 0} (α := Nat) (P := fun _ => True) (IB.fn fun _ => trivial)

-- and at a `Type`-valued `P`, so it does not
/-- info: 0 -/
#guard_msgs in
#eval iTag.{0, 1} (α := Nat) (P := fun _ => Nat) (IB.fn fun n => n)

/-- info: 'iTag' does not depend on any axioms -/
#guard_msgs in
#print axioms iTag

/-! ### Three universe parameters, used unevenly

`MB` uses only `u` and `MC` uses all three. They are in different components of
the data-only dependency graph, which is what lets them sit at different
universes. Note that a field of type `Type v` needs the member at `v + 1`, not
at `v`. -/

mutual_multiuniverse
inductive MA : Prop where
  | fromB : MB → MA
  | fromC : MC → MA
inductive MB : Type u where
  | leaf : Nat → MB
  | fromA : MA → MB
inductive MC : Type (max u (max (v + 1) (w + 1))) where
  | fromB : MB → MC
  | big : Type v → Type w → MC
end

/-- info: MC.{u, v, w} : Type (max u (v + 1) (w + 1)) -/
#guard_msgs in
#check MC

def mTag : MC.{u, v, w} → Nat :=
  @MC.mutualRec (fun _ => True) (fun _ => Nat) (fun _ => Nat)
    (fun _ _ => trivial) (fun _ _ => trivial)
    (fun n => n) (fun _ _ => 0) (fun _ ih => ih + 1) (fun _ _ => 0)

/-- info: 5 -/
#guard_msgs in
#eval mTag.{0, 0, 0} (MC.fromB (MB.leaf 4))

/-! ### Members of one data component share a universe

`KB` and `KC` hold each other, so each one's universe has to be at least the
other's -- they have to be equal. That still leaves them polymorphic, it just
means one variable does for both. -/

mutual_multiuniverse
inductive KA : Prop where
  | mk : KB → KA
inductive KB : Type u where
  | leaf : Nat → KB
  | toC : KC → KB
inductive KC : Type u where
  | fromB : KB → KC
  | fromA : KA → KC
end

def kTag : KB.{u} → Nat :=
  @KB.mutualRec (fun _ => True) (fun _ => Nat) (fun _ => Nat)
    (fun _ _ => trivial) (fun n => n) (fun _ ih => ih + 1)
    (fun _ ih => ih + 1) (fun _ _ => 0)

/-- info: 8 -/
#guard_msgs in
#eval kTag.{0} (KB.toC (KC.fromB (KB.leaf 6)))

/-! ### `Sort (max 1 u)`

Not syntactically `Type _`, but never `Prop` either, so it is a data member. -/

mutual_multiuniverse
inductive SA : Prop where
  | mk : SB → SA
inductive SB : Sort (max 1 u) where
  | leaf : Nat → SB
  | fromA : SA → SB
end

/-- info: SB.{u} : Sort (max 1 u) -/
#guard_msgs in
#check SB

def sbTag : SB.{u} → Nat :=
  @SB.mutualRec (fun _ => True) (fun _ => Nat) (fun _ _ => trivial)
    (fun n => n) (fun _ _ => 0)

/-- info: 4 -/
#guard_msgs in
#eval sbTag.{0} (SB.leaf 4)

/-! ### Indices and universe polymorphism together -/

mutual_multiuniverse
inductive XEv : Nat → Prop where
  | zero : XEv 0
  | succ : (n : Nat) → XOd n → XEv (n + 1)
inductive XOd : Nat → Type u where
  | one : XOd 1
  | succ : (n : Nat) → XEv (n + 1) → XOd n → Nat → XOd (n + 2)
end

/-- info: XOd.{u} : Nat → Type u -/
#guard_msgs in
#check XOd

def xSum : (n : Nat) → XOd.{u} n → Nat :=
  fun n t => @XOd.mutualRec (fun _ _ => True) (fun _ _ => Nat)
    trivial (fun _ _ _ => trivial) 0 (fun _ _ _ k _ ih => ih + k) n t

/-- info: 10 -/
#guard_msgs in
#eval xSum.{0} 5 (.succ 3 (.succ 3 (.succ 1 (.succ 1 .one) .one 4)) (.succ 1 (.succ 1 .one) .one 4) 6)

/-! ### Small elimination at a variable universe

Universes are derived per member, elimination is not: the motives may all land
in `Prop` whatever `u` is. -/

example (b : PB.{u}) : True :=
  @PB.mutualRec (fun _ => True) (fun _ => True) (fun _ => True)
    (fun _ _ => trivial) (fun _ _ => trivial)
    (fun _ => trivial) (fun _ _ => trivial) (fun _ _ => trivial)
    (fun _ _ => trivial) (fun _ => trivial) (fun _ _ _ _ => trivial) b

end

/-! ## What makes the recursors computable

The code generator compiles no recursor application, so each data member's
`X.mutualRec` is paired with an implementation that does the same recursion by
cases, and a `@[csimp]` theorem relating the two.  Both are ordinary
declarations under predictable names; the theorem is proved rather than
asserted, and the implementation is checked to terminate by Lean's own
structural recursion.

`CD.branch` also makes this the case where a *data* member recurses under a
binder, so the implementation has to as well. -/

mutual_multiuniverse
inductive CP : Prop where
  | mk : CD → CP
inductive CD : Type 0 where
  | leaf : Nat → CD
  | branch : (Nat → CD) → CD
end

/-- info: CD.mutualRec.eq_impl : @CD.mutualRec = @CD.mutualRec.impl -/
#guard_msgs in
#check @CD.mutualRec.eq_impl

-- `CD.branch` is infinitary, so the `Prop` member's recursor selects witnesses
-- pointwise as above -- but the data member's recursor never touches the
-- shadow, and neither does the implementation
/-- info: 'CP.mutualRec' depends on axioms: [Classical.choice] -/
#guard_msgs in
#print axioms CP.mutualRec

/-- info: 'CD.mutualRec' does not depend on any axioms -/
#guard_msgs in
#print axioms CD.mutualRec

-- `funext` is all the proof needs, and it stays inside the theorem
/-- info: 'CD.mutualRec.eq_impl' depends on axioms: [Quot.sound] -/
#guard_msgs in
#print axioms CD.mutualRec.eq_impl

/-- info: 'CD.mutualRec.impl' does not depend on any axioms -/
#guard_msgs in
#print axioms CD.mutualRec.impl

def cdSum : CD → Nat :=
  @CD.mutualRec (fun _ => True) (fun _ => Nat)
    (fun _ _ => trivial)
    (fun n => n) (fun _ ih => ih 3)

example : cdSum (CD.branch fun n => CD.leaf (n * 2)) = 6 := rfl

/-- info: 6 -/
#guard_msgs in
#eval cdSum (CD.branch fun n => CD.leaf (n * 2))

-- two levels of `branch`, so the implementation recurses under a binder twice
/-- info: 33 -/
#guard_msgs in
#eval cdSum (CD.branch fun n => CD.branch fun m => CD.leaf (n * 10 + m))

-- neither the implementation nor its theorem reaches the term
/-- info: 'cdSum' does not depend on any axioms -/
#guard_msgs in
#print axioms cdSum

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

-- the alias still gets an implementation and a `@[csimp]` theorem, so `mutualRec`
-- is computable here as well, even though the recursor it unfolds to is not
def t1Depth : T1 → Nat :=
  @T1.mutualRec (fun _ => Nat) (fun _ => Nat)
    (fun _ ih => ih + 1) (fun _ ih => ih + 1) 0

example : t1Depth (T1.mk (T2.mk (T1.mk T2.stop))) = 3 := rfl

/-- info: 3 -/
#guard_msgs in
#eval t1Depth (T1.mk (T2.mk (T1.mk T2.stop)))

/-! A homogeneous block can still fall into several components: `U` mentions
`V`, but not the other way round.  The implementations follow the components
rather than the block, so `U.mutualRec.impl` does not recurse into `V` itself --
it calls `V.mutualRec`, and `V`'s own `@[csimp]` theorem, already registered by
then, is what puts the code there. -/

mutual_multiuniverse
inductive V1 : Type where
  | nil : V1
  | wrap : V1 → V1
inductive U1 : Type where
  | mk : V1 → U1
  | more : U1 → U1
end

/-- info: U1.mutualRec.eq_impl : @U1.mutualRec = @U1.mutualRec.impl -/
#guard_msgs in
#check @U1.mutualRec.eq_impl

/-- info: V1.mutualRec.eq_impl : @V1.mutualRec = @V1.mutualRec.impl -/
#guard_msgs in
#check @V1.mutualRec.eq_impl

def u1Len : U1 → Nat :=
  @U1.mutualRec (fun _ => Nat) (fun _ => Nat) 0 (fun _ ih => ih + 1) (fun _ ih => ih)
    (fun _ ih => ih + 100)

example : u1Len (U1.more (U1.mk (V1.wrap (V1.wrap V1.nil)))) = 102 := rfl

/-- info: 102 -/
#guard_msgs in
#eval u1Len (U1.more (U1.mk (V1.wrap (V1.wrap V1.nil))))

/-- info: 'u1Len' does not depend on any axioms -/
#guard_msgs in
#print axioms u1Len

/-! ## An all-`Prop` homogeneous block

There is nothing to compute here, so no implementation is emitted: the recursors
are proofs and are erased.  Such a block still has to come out of the native
path in one piece. -/

mutual_multiuniverse
inductive PEven : Nat → Prop where
  | zero : PEven 0
  | succ : (n : Nat) → POdd n → PEven (n + 1)
inductive POdd : Nat → Prop where
  | succ : (n : Nat) → PEven n → POdd (n + 1)
end

example : @PEven.mutualRec = @PEven.rec := rfl

example : POdd 3 := .succ 2 (.succ 1 (.succ 0 .zero))

theorem POdd.ne_zero : ∀ n, POdd n → n ≠ 0 :=
  @POdd.mutualRec (fun _ _ => True) (fun n _ => n ≠ 0)
    trivial (fun _ _ _ => trivial) (fun n _ _ => Nat.succ_ne_zero n)

-- `propext` comes from `Nat.succ_ne_zero`, not from the block
/-- info: 'POdd.ne_zero' depends on axioms: [propext] -/
#guard_msgs in
#print axioms POdd.ne_zero

/-- info: 'POdd.mutualRec' does not depend on any axioms -/
#guard_msgs in
#print axioms POdd.mutualRec

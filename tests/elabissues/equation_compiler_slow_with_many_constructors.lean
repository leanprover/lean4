/-
This file contains an example of an inductive type with many constructors,
for which pattern matching is expensive enough to noticeably slow down Emacs.
Note that the annoyance is magnified with the current Emacs mode
because every modification to the inductive type immediately triggers
recompilation of the downstream equations.
-/

inductive Op : Type
| add, mul, inv, div, sub, fact, pow

inductive Term : Type
| ofInt  : Int → Term
| var    : Nat → Term
| varPow : Nat → Nat → Term
| app    : Op → Term → Term → Term

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
| fact0     : Proof
| factS     : Nat → Proof
| tpow0     : Term → Proof
| tpow1     : Term → Proof
| tpowS     : Term → Term → Proof
| ofIntAdd  : Int → Int → Proof
| ofIntMul  : Int → Int → Proof
| subDef    : Term → Term → Proof
| powZero   : Nat → Proof
| powOne    : Nat → Proof
| powMerge  : Nat → Nat → Nat → Proof
| powMergeL : Nat → Nat → Nat → Term → Proof
| mulInvCan : Term → Proof
| invMulCan : Term → Proof
| fuse      : Term → Term → Proof
| fuseL     : Term → Term → Term → Proof
| oneDivInv : Term → Proof
| oneInvEq  : Proof
| divDef    : Term → Term → Proof
| congrArg₁ : Op → Proof → Term → Proof
| congrArg₂ : Op → Term → Proof → Proof
| congrArgs : Op → Proof → Proof → Proof
| refl      : Term → Proof
| trans     : Proof → Proof → Proof

open Proof

structure Result : Type :=
(val  : Term)
(pf   : Proof)

set_option eqn_compiler.max_steps 5000

def mergeCongr (op : Op) (x₁ y₁ : Term) : Result → Result → Result
| ⟨_, refl _⟩, ⟨_, refl _⟩ => ⟨app op x₁ y₁, refl $ app op x₁ y₁⟩
| ⟨x₂, px⟩,    ⟨_, refl _⟩ => ⟨app op x₂ y₁, congrArg₁ op px y₁⟩
| ⟨_, refl _⟩, ⟨y₂, py⟩    => ⟨app op x₁ y₂, congrArg₂ op x₁ py⟩
| ⟨x₂, px⟩,    ⟨y₂, py⟩    => ⟨app op x₂ y₂, congrArgs op px py⟩

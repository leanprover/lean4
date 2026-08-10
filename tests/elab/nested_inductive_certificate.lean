import Lean

/-!
Every nested inductive the kernel compiles must have a certificate: a model, bridges relating
each auxiliary copy to the type it stands for, surrogate constructors and recursors over that
model, and a proof of every computation rule the declaration states.

`environment::add_inductive` certifies each declaration as it makes it, so declaring a shape is
the test: one whose certificate does not answer, or leaves a computation rule open, is rejected.
The shapes below are chosen to cover the awkward cases.
-/

inductive Tree where
  | node : List Tree → Tree

/-- Iterated nesting: two auxiliary copies, the outer defined via the inner. -/
inductive T where
  | mk : List (Option T) → T

/-- The two occurrences share a head symbol, so aux lookup must compare applied parameters. -/
inductive U where
  | mk : List (List U) → U

inductive V (α : Type) where
  | mk : List (V α) → α → V α

/-- A reflexive occurrence: the nesting sits under a binder. -/
inductive P where
  | mk : (Nat → List P) → P

/-- A type former with a function-typed field, to push the nesting under a binder. -/
inductive Cont (α : Type) where
  | mk : (Nat → α) → Cont α

/-- Here the Pi is inside the *auxiliary copy*, which is what forces the PI layer. -/
inductive W where
  | mk : Cont (List W) → W

/-- `Y` is itself a nested inductive... -/
inductive Y (α : Type) where
  | mk : List (Y α) → α → Y α

/-- ...so `Z`, which nests under `Y`, exercises nesting-under-nested. -/
inductive Z where
  | mk : Y Z → Z

/-- An indexed family, to nest under. -/
inductive Fam (α : Type) : Nat → Type where
  | z : Fam α 0
  | s : {n : Nat} → α → Fam α n → Fam α (n+1)

/-- Lean 4 accepts this: the nested occurrence carries an index. -/
inductive Idx where
  | mk : Fam Idx 2 → Idx

/-- Indexed nesting under a parameterized declaration, so parameters and indices interleave. -/
inductive IdxP (α : Type) where
  | mk : Fam (IdxP α) 3 → α → IdxP α

/-- An indexed auxiliary copy inside a non-indexed one. -/
inductive IdxL where
  | mk : List (Fam IdxL 2) → IdxL

/-- An indexed auxiliary copy inside another indexed one. -/
inductive IdxF where
  | mk : Fam (Fam IdxF 1) 2 → IdxF

/-- Indices pushed through the PI layer. -/
inductive IdxC where
  | mk : Cont (Fam IdxC 2) → IdxC

/--
The *declared* type is indexed here, which is the other direction: the main recursor takes an
index and each minor's transport has to be stated at the indices its own constructor determines.
-/
inductive IdxD : Bool → Type where
  | t : List (IdxD true) → IdxD true
  | f : IdxD false

/--
The nested occurrence carries a lambda as a parameter: `Sigma`'s `β` is `fun I => I → SigmaNest`, so
the auxiliary copy's second field has type `(fun I => I → SigmaNest) fst`, a redex.

This is also where the model is reflexive and the declaration is not, which is why the kernel
compares the flag in one direction only. `is_reflexive` asks `is_pi` of each constructor field, and
that field is a redex hiding the binder; the model has already reduced it to `fst → SigmaNest`,
which really is a function into the type. Beta only ever exposes more `∀`, so a declaration
reflexive against a model that is not would mean the model has lost a field. Comparing the two for
equality instead would reject this declaration.
-/
inductive SigmaNest : Type (u + 1)
  | node : (Σ (I : Type u), I → SigmaNest) → SigmaNest

/-!
An unsafe nested inductive is declared without a certificate. Nothing could certify one: the bridges
are definitions and the rule proofs are theorems, and neither may mention an unsafe constant. Such a
declaration is outside the kernel's guarantees to begin with.

Pinned because it is the case the certification deliberately skips, so it is the one that breaks
were the skip to be tightened into a rejection.
-/
unsafe inductive UTree where
  | node : List UTree → UTree

unsafe inductive UParam (α : Type) where
  | mk : List (UParam α) → α → UParam α

unsafe def usize : UTree → Nat
  | .node ts => ts.foldl (fun a t => a + usize t) 1

/-- info: 4 -/
#guard_msgs in
#eval usize (.node [.node [], .node [.node []]])

/-!
A nested occurrence may only be parameterised by the declaration's own parameters. Here `Box`'s
parameter depends on the constructor's field `b`, so no single auxiliary copy stands for the
occurrence and the elimination rejects the declaration before there is anything to certify.
-/
inductive Box (α : Type) where
  | mk : α → Box α

/--
error: (kernel) invalid nested inductive datatype 'Box', nested inductive datatypes parameters cannot contain local variables.
-/
#guard_msgs in
inductive T2 where
  | mk : (b : Bool) → Box (if b then T2 else Nat) → T2

/-!
The elimination accepts a constructor whose type refers forward to another constructor of the same
block, which no model can stand for: the bridges are built in the environment as it stood before the
declaration, where that constructor does not yet exist. The certificate is what rejects it.

This is also the file's tripwire. Every declaration above is accepted whether or not the certificate
is consulted, so this is the one that breaks were the check to stop running at all.
-/
inductive ECFBox (α : Type) (_ : α) : Type where
  | mk

open Lean in
/--
error: (kernel) uncertified nested inductive type 'EarlierCtorForward': (kernel) unknown constant 'EarlierCtorForward.base'
-/
#guard_msgs in
run_meta do
  let name := `EarlierCtorForward
  let self := mkConst name
  let laterTy := mkForall `box .default
    (mkApp2 (mkConst ``ECFBox) self (mkConst (name ++ `base))) self
  addDecl <| .inductDecl [] 0 [{
    name, type := mkSort 1,
    ctors := [{ name := name ++ `base, type := self },
              { name := name ++ `later, type := laterTy }] }] false

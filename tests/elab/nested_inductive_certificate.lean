import Lean

/-!
Every nested inductive the kernel compiles must have a certificate: a model, bridges relating
each auxiliary copy to the type it stands for, surrogate constructors and recursors over that
model, and a proof of every computation rule the declaration states.

This runs the generator over a set of shapes chosen to cover the awkward cases, and then over
every nested inductive reachable in the environment, so the whole of core acts as the corpus. It
is silent on success and throws on the first block that fails or leaves a rule open.

The last block covers `NestedGen.certify`, which reaches the generator through a kernel environment
rather than the one being elaborated, as `environment::add_inductive` does.
-/

open Lean Meta NestedGen

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

/-- Certify `n`, throwing if any of its computation rules is left open. -/
private def certify (n : Name) (pre : Name) : MetaM Unit := do
  let res ← buildModel n pre
  unless res.openRules.isEmpty do
    throwError "{n}: computation rule(s) left uncertified: {res.openRules}"
  -- the correspondence has to cover the declaration's own type and constructors at least
  unless res.subst.size ≥ 2 do
    throwError "{n}: correspondence covers only {res.subst.size} constant(s)"

run_meta do
  let shapes := #[``Tree, ``T, ``U, ``V, ``P, ``W, ``Z,
                  ``Idx, ``IdxP, ``IdxL, ``IdxF, ``IdxC, ``IdxD, ``SigmaNest]
  for i in [0 : shapes.size] do
    certify shapes[i]! (`Shape ++ Name.mkSimple (toString i))

/-!
The model can be reflexive where the declaration is not, which is why the kernel compares the flag in
one direction only. `is_reflexive` asks `is_pi` of each constructor field, and `SigmaNest`'s field is
`(fun I => I → SigmaNest) fst`, a redex that hides the binder; the model has already reduced it to
`fst → SigmaNest`, which really is a function into the type.

Pinned because it is the asymmetry the kernel's check is shaped around: beta only ever exposes more
`∀`, so a declaration reflexive against a model that is not would mean the model has lost a field.
-/
run_meta do
  let res ← buildModel ``SigmaNest `ReflAsym
  let declared := (← getConstInfoInduct ``SigmaNest).isReflexive
  let some derived := res.reflexive[0]?
    | throwError "the model says nothing about SigmaNest's reflexivity"
  unless !declared && derived do
    throwError "expected the declaration not reflexive and the model reflexive, got \
      {declared} and {derived}"

run_meta do
  let env ← getEnv
  let mut targets := #[]
  for (n, ci) in env.constants.toList do
    if let .inductInfo iv := ci then
      if iv.numNested > 0 && !n.isInternal && !iv.isUnsafe && iv.all.head! == n then
        targets := targets.push n
  let sorted := targets.qsort fun a b => a.toString < b.toString
  -- a shrinking corpus would silently weaken this test, so pin a floor
  unless sorted.size ≥ 45 do
    throwError "expected at least 45 nested inductives in the corpus, found {sorted.size}"
  for i in [0 : sorted.size] do
    certify sorted[i]! (`Corpus ++ Name.mkSimple (toString i))

run_meta do
  let kenv := (← getEnv).toKernelEnv
  for n in #[``Tree, ``T, ``U, ``V, ``P, ``W, ``Z,
             ``Idx, ``IdxP, ``IdxL, ``IdxF, ``IdxC, ``IdxD, ``Lean.Syntax] do
    match ← NestedGen.certify kenv n with
    | .error msg   => throwError "{n}: {msg}"
    | .ok none     => throwError "{n}: reported as having no nested occurrence"
    | .ok (some c) =>
      -- What the kernel requires: the declaration's names answered by definitions over the model,
      -- which is what stops the rules being restated about the very constants they license.
      let some ci := c.env.find? (`_surr ++ n) | throwError "{n}: nothing realises the type"
      let .defnInfo _ := ci | throwError "{n}: the type is realised by {ci.name}, not a definition"
      if c.recs.isEmpty then throwError "{n}: no recursors derived"

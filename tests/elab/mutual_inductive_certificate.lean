import Lean

/-!
A mutual inductive block collapses to a single inductive family indexed by an enumeration of the
block's types. This runs that reduction over a set of shapes chosen to cover the awkward cases, and
then over every mutual block reachable in the environment, checking three things of each:

* the recursors derived from the model are the ones the kernel declared, binder for binder;
* every type, constructor and recursor of the block is realised by a definition over the model;
* every computation rule the kernel made definitional already holds definitionally over the model,
  so nothing has to be proved.

It is silent on success and throws on the first block that fails.
-/

open Lean Meta MutualGen

/-! Plain mutual recursion. -/
mutual
inductive Ev where
  | zero : Ev
  | succ : Od → Ev
inductive Od where
  | succ : Ev → Od
end

/-! Parameters, shared across the block as the kernel requires. -/
mutual
inductive Forest (α : Type u) where
  | nil  : Forest α
  | cons : Tree α → Forest α → Forest α
inductive Tree (α : Type u) where
  | node : α → Forest α → Tree α
end

/-! Three components, so the index enumeration is not a `Bool` in disguise. -/
mutual
inductive A3 where | a : B3 → A3
inductive B3 where | b : C3 → B3
inductive C3 where | c : A3 → C3 | stop : C3
end

/-! A component with no constructors at all. -/
mutual
inductive Live where | mk : Dead → Live
inductive Dead where
end

/-! Not recursive, which the block's metadata has to report faithfully. -/
mutual
inductive Flat where | mk : Nat → Flat
inductive Flat' where | mk : Bool → Flat'
end

/-! Reflexive: a field is a function into the block, which drives `below` and `brecOn`. -/
mutual
inductive Node where
  | mk : (Nat → Branch) → Node
inductive Branch where
  | leaf : Branch
  | more : Node → Branch
end

/-! Implicit and instance-implicit fields, whose annotations survive into the minor premises. -/
mutual
inductive Impl where
  | mk : {α : Type} → [inst : Inhabited α] → α → Impl' → Impl
inductive Impl' where
  | mk : Impl → Impl'
  | nil : Impl'
end

/-!
A mutual inductive predicate, which eliminates only into `Prop`, so the derived recursors have no
universe parameter of their own.
-/
mutual
inductive EvP : Prop where
  | zero : EvP
  | succ : OdP → EvP
inductive OdP : Prop where
  | succ : EvP → OdP
end

/-! Indices, of differing arity across the block, so the enumeration is not a plain tag. -/
mutual
inductive Even : Nat → Type where
  | zero : Even 0
  | succ : {n : Nat} → Odd n → Even (n + 1)
inductive Odd : Nat → Type where
  | succ : {n : Nat} → Even n → Odd (n + 1)
end

/-! One component indexed and one not, so the enumeration's constructors differ in arity. -/
mutual
inductive Mixed : Bool → Type where
  | t : Plain → Mixed true
  | f : Mixed false
inductive Plain where
  | mk : Mixed true → Plain
end

/-! An index in a universe of its own, which the enumeration has to be big enough to hold. -/
mutual
inductive Tagged (α : Type u) : Type u → Type (u + 1) where
  | mk : Other α → Tagged α α
inductive Other (α : Type u) : Type (u + 1) where
  | mk : α → Other α
  | wrap : Tagged α α → Other α
end

/-! An indexed mutual inductive predicate, which eliminates only into `Prop`. -/
mutual
inductive EvenP : Nat → Prop where
  | zero : EvenP 0
  | succ : {n : Nat} → OddP n → EvenP (n + 1)
inductive OddP : Nat → Prop where
  | succ : {n : Nat} → EvenP n → OddP (n + 1)
end

/-!
An unsafe block gets its recursors derived from the model like any other, but nothing certifies
them: the realisations are unsafe definitions, so the kernel takes neither them nor the rules on
their word. Pinned because it is the case with no certificate, so it is the one that breaks when the
uncertified path is removed rather than kept deliberately.
-/
mutual
unsafe inductive UEv where
  | zero : UEv
  | succ : UOd → UEv
unsafe inductive UOd where
  | succ : UEv → UOd
end

mutual
unsafe def uevSize : UEv → Nat
  | .zero => 0
  | .succ o => uodSize o + 1
unsafe def uodSize : UOd → Nat
  | .succ e => uevSize e + 1
end

/-- info: 2 -/
#guard_msgs in
#eval uevSize (.succ (.succ .zero))

/-- Structural equality of expressions, binder names and annotations included. -/
private partial def strictEq : Expr → Expr → Bool
  | .forallE n₁ d₁ b₁ i₁, .forallE n₂ d₂ b₂ i₂
  | .lam n₁ d₁ b₁ i₁, .lam n₂ d₂ b₂ i₂ =>
    n₁ == n₂ && i₁ == i₂ && strictEq d₁ d₂ && strictEq b₁ b₂
  | .letE n₁ t₁ v₁ b₁ _, .letE n₂ t₂ v₂ b₂ _ =>
    n₁ == n₂ && strictEq t₁ t₂ && strictEq v₁ v₂ && strictEq b₁ b₂
  | .app f₁ a₁, .app f₂ a₂ => strictEq f₁ f₂ && strictEq a₁ a₂
  | .proj s₁ i₁ e₁, .proj s₂ i₂ e₂ => s₁ == s₂ && i₁ == i₂ && strictEq e₁ e₂
  | .mdata _ e₁, e₂ => strictEq e₁ e₂
  | e₁, .mdata _ e₂ => strictEq e₁ e₂
  | e₁, e₂ => e₁ == e₂

/--
Reduce `n`'s block to a single inductive and check the result against the declaration the kernel
made: the recursors it derived, the realisations it added, and the rules it claims are definitional.
-/
private def certify (n : Name) (pre : Name) : MetaM Unit := do
  let iv ← getConstInfoInduct n
  let res ← buildModel n pre
  let sur : Name → Name := (`_surr ++ pre ++ ·)
  let mut own : NameSet := {}
  for m in iv.all do
    let jv ← getConstInfoInduct m
    own := own.insert m |>.insert (mkRecName m)
    for c in jv.ctors do
      own := own.insert c
  let fix (e : Expr) : Expr := e.replace fun
    | .const c us => if own.contains c then some (.const (sur c) us) else none
    | _ => none
  -- what the kernel derived from the same block, as ground truth
  unless res.recs.size == iv.all.length do
    throwError "{n}: {res.recs.size} recursors derived for a block of {iv.all.length}"
  unless res.recursive == iv.isRec do
    throwError "{n}: derived isRec {res.recursive}, declared {iv.isRec}"
  unless res.reflexive == iv.isReflexive do
    throwError "{n}: derived isReflexive {res.reflexive}, declared {iv.isReflexive}"
  for r in res.recs do
    let rv ← getConstInfoRec r.name
    unless r.levelParams == rv.levelParams do
      throwError "{r.name}: derived level parameters {r.levelParams}, declared {rv.levelParams}"
    unless strictEq r.type rv.type do
      throwError "{r.name} derives as{indentExpr r.type}\nbut the kernel declared{indentExpr rv.type}"
    unless r.rules.size == rv.rules.length do
      throwError "{r.name}: {r.rules.size} rules derived, {rv.rules.length} declared"
    for ((c, nf, rhs), rd) in r.rules.zip rv.rules.toArray do
      unless c == rd.ctor && nf == rd.nfields do
        throwError "{r.name}: rule derived as {c}/{nf}, declared {rd.ctor}/{rd.nfields}"
      unless strictEq rhs rd.rhs do
        throwError "{r.name}: the rule for {rd.ctor} derives as{indentExpr rhs}\n\
          but the kernel declared{indentExpr rd.rhs}"
    -- the realisation, which is what the kernel would require before declaring anything
    for m in own do
      let some ci := (← getEnv).find? (sur m) | throwError "{n}: nothing realises {m}"
      let .defnInfo _ := ci | throwError "{n}: {m} is realised by {ci.name}, not a definition"
    -- and what it would then check of the rules: that the model already validates them
    let lvls := r.levelParams.map Level.param
    forallBoundedTelescope (fix r.type) (rv.numParams + rv.numMotives + rv.numMinors) fun args _ => do
      let params := args.extract 0 rv.numParams
      for (c, _, rhs) in r.rules do
        let cTy ← instantiateForall (fix (← getConstInfo c).type) params
        forallTelescope cTy fun fields concl => do
          -- the indices the rule fires at are the ones this constructor returns
          let indices := concl.getAppArgs.extract rv.numParams concl.getAppArgs.size
          let cApp := mkAppN (mkConst (sur c) (iv.levelParams.map Level.param)) (params ++ fields)
          let lhs := mkAppN (mkConst (sur r.name) lvls) (args ++ indices ++ #[cApp])
          unless ← isDefEq lhs (mkAppN (fix rhs) (args ++ fields)) do
            throwError "{r.name}: the rule for {c} does not hold over the model"

run_meta do
  let shapes := #[``Ev, ``Forest, ``A3, ``Live, ``Flat, ``Node, ``Impl, ``EvP,
                  ``Even, ``Mixed, ``Tagged, ``EvenP, ``UEv]
  for i in [0 : shapes.size] do
    certify shapes[i]! (`Shape ++ Name.mkSimple (toString i))

run_meta do
  let env ← getEnv
  let mut targets := #[]
  for (n, ci) in env.constants.toList do
    if let .inductInfo iv := ci then
      if iv.all.length ≥ 2 && iv.numNested == 0 && !iv.isUnsafe && !n.isInternal
          && iv.all.head! == n then
        targets := targets.push n
  let sorted := targets.qsort fun a b => a.toString < b.toString
  -- a shrinking corpus would silently weaken this test, so pin a floor
  unless sorted.size ≥ 20 do
    throwError "expected at least 20 mutual blocks in the corpus, found {sorted.size}"
  for i in [0 : sorted.size] do
    certify sorted[i]! (`Corpus ++ Name.mkSimple (toString i))

import Lean.Meta.Sym
open Lean Meta Sym
set_option sym.debug true

/-!
`isDefEqS` solves `?f a₁ … aₙ =?= s` when the arguments form a nested pattern: each argument is a
variable bound by the binders that `isDefEqS` opens, a structure instance whose fields satisfy this
condition, or a term of a subsingleton type.
-/

/--
`#unify_s f : T, lhs =?= rhs` replaces the variable `f` of `lhs` with a fresh metavariable `?f : T`,
unifies `lhs` and `rhs` with `isDefEqS`, and logs the result and the value of `?f`.
-/
elab "#unify_s " f:ident " : " type:term ", " lhs:term " =?= " rhs:term : command =>
  Elab.Command.liftTermElabM do
    let type ← Elab.Term.elabType type
    let lhs ← Elab.Term.elabTerm (← `(fun ($f : $(← Elab.Term.exprToSyntax type)) => $lhs)) none
    Elab.Term.synthesizeSyntheticMVarsNoPostponing
    let m ← mkFreshExprMVar type (userName := f.getId)
    let lhs := (← instantiateMVars lhs).beta #[m]
    let rhs ← Elab.Term.elabTerm rhs (← inferType lhs)
    Elab.Term.synthesizeSyntheticMVarsNoPostponing
    let rhs ← instantiateMVars rhs
    SymM.run do
      let lhs ← shareCommon lhs
      let rhs ← shareCommon rhs
      let ok ← isDefEqS lhs rhs
      if ok then
        Meta.check (← instantiateMVars m)
        unless (← Meta.isDefEq (← instantiateMVars lhs) rhs) do
          throwError "the solution does not satisfy the constraint"
      logInfo m!"{ok}: {← instantiateMVars m}"

/-- info: true: fun x => x.snd + x.fst -/
#guard_msgs in
#unify_s f : Nat × Nat → Nat, fun (a b : Nat) => f (a, b) =?= fun a b => b + a

/-- info: true: fun x a => a * 2 -/
#guard_msgs in
#unify_s f : Unit → Nat → Nat, fun (a : Nat) => f () a =?= fun a => a * 2

/-- info: true: fun x => x.fst.fst + x.fst.snd * x.snd -/
#guard_msgs in
#unify_s f : (Nat × Nat) × Nat → Nat, fun (a b c : Nat) => f ((a, b), c) =?= fun a b c => a + b * c

/-- info: true: fun a x => a + x.fst - x.snd.fst -/
#guard_msgs in
#unify_s f : Nat → Nat × Nat × Unit → Nat, fun (a b c : Nat) => f a (b, (c, ())) =?= fun a b c => a + b - c

/-- info: true: fun x a => a -/
#guard_msgs in
#unify_s f : 0 ≤ 0 → Nat → Nat, fun (a : Nat) => f (Nat.le_refl 0) a =?= fun a => a

/-- info: true: fun x => ↑x.snd + x.fst -/
#guard_msgs in
#unify_s f : (n : Nat) × Fin n → Nat, fun (n : Nat) (i : Fin n) => f ⟨n, i⟩ =?= fun n i => i.val + n

/-! A leaf of a subsingleton type can contain variables, including variables of the spine. -/

/-- info: true: fun x => x.val + 1 -/
#guard_msgs in
#unify_s f : {n : Nat // n ≤ n} → Nat, fun (a : Nat) => f ⟨a, Nat.le_refl a⟩ =?= fun a => a + 1

/-- info: true: fun x => x.fst -/
#guard_msgs in
#unify_s f : Nat × Unit → Nat, fun (g : Nat → Unit) (a : Nat) => f (a, g a) =?= fun g a => a

/-- info: true: fun x => x.fst -/
#guard_msgs in
#unify_s f : Nat × Unit × Unit → Nat, fun (a : Nat) (u : Unit) => f (a, u, u) =?= fun a u => a

/-! A field that is a closed term of a type with two elements is not a nested pattern. -/

/-- info: false: ?f -/
#guard_msgs in
#unify_s f : Nat × Nat → Nat, fun (a : Nat) => f (a, 0) =?= fun a => a

/-! A variable of a type with two elements that occurs twice in the spine is not a nested pattern. -/

/-- info: false: ?f -/
#guard_msgs in
#unify_s f : Nat × Nat → Nat, fun (a : Nat) => f (a, a) =?= fun a => a

/-! A field of a type with two elements that is an application of a variable is not a nested
pattern. -/

/-- info: false: ?f -/
#guard_msgs in
#unify_s f : Nat × Nat → Nat, fun (a : Nat) => f (a, a + 1) =?= fun a => a

/-! A rule pattern whose higher-order variable `f` meets a nested pattern. -/

opaque P : (Nat → Nat → Nat) → Prop
axiom P_pair (f : Nat × Nat → Nat) : P (fun a b => f (a, b))

opaque Q : (Nat → Nat) → Prop
axiom Q_unit (f : Nat → Unit → Nat) : Q (fun a => f a ())

def testRule (rule target : Name) : SymM Unit := do
  let p ← mkPatternFromDecl rule
  let e ← shareCommon (← getConstInfo target).value!
  let some r ← p.match? e | throwError "no match"
  logInfo <| mkAppN (mkConst rule r.us) r.args

def tgtP := P (fun a b => b * a + 1)
def tgtQ := Q (fun a => a + 2)

/-- info: P_pair fun x => x.snd * x.fst + 1 -/
#guard_msgs in
#eval SymM.run <| testRule ``P_pair ``tgtP

/-- info: Q_unit fun a x => a + 2 -/
#guard_msgs in
#eval SymM.run <| testRule ``Q_unit ``tgtQ

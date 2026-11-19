import Lean

/-!
# Rewriting, normalization and proof building with `expr` quotations

A tiny arithmetic normalizer and a few goal-transforming tactics built from `expr` quotations:

- `natStep?`: consecutive single-column arms, automatically indexed by a discrimination tree,
  each returning the rewritten term and an equality proof built from a term template;
- `nat_norm`: contextual `rewrite` driven by `subterms`, `kabstract` and `MVarId.rewrite`;
- `succ_to_add`: contextual `change` via `ExprContext.fill` and `replaceTargetDefEq`;
- `split_bool_match`: case analysis on `matchDiscriminants` filtered by a typed pattern;
- `and_skeleton`: proof skeletons whose `?l`/`?r` holes become the new goals;
- how the matching relation (`/structural`, `/reducible`, `/instances`, `/defeq`, `±flags`,
  `[items]`, `match (modulo := rel)`) decides which spellings of a term a pattern accepts.
-/

namespace ExprQuotRewriting
open Lean Meta Elab Tactic

/-- One normalization step `e = e'` with its proof, or `none` if no rule applies at the root. -/
def natStep? (e : Expr) : MetaM (Option (Expr × Expr)) := do
  match e with
  | `(expr| (?x : Nat) + 0) => return some (x, ← `(expr| Nat.add_zero $x))
  | `(expr| 0 + (?x : Nat)) => return some (x, ← `(expr| Nat.zero_add $x))
  | `(expr| (?x : Nat) * 1) => return some (x, ← `(expr| Nat.mul_one $x))
  | `(expr| 1 * (?x : Nat)) => return some (x, ← `(expr| Nat.one_mul $x))
  | `(expr| (?x : Nat) * 0) => return some (mkNatLit 0, ← `(expr| Nat.mul_zero $x))
  | `(expr| (?x : Nat) - $x) => return some (mkNatLit 0, ← `(expr| Nat.sub_self $x))
  | _ => return none

/-- `nat_norm`: rewrite with `natStep?` at the outermost matching subterm until none is left. -/
elab "nat_norm" : tactic => withMainContext do
  let mut goal ← getMainGoal
  repeat
    let tgt ← instantiateMVars (← goal.getType)
    let mut eq? := none
    for (sub, _) in subterms tgt do
      if let some (_, pf) ← natStep? sub then
        eq? := some pf
        break
    let some eq := eq? | break
    let r ← goal.rewrite tgt eq
    goal ← goal.replaceTargetEq r.eNew r.eqProof
  replaceMainGoal (if (← observing? goal.refl).isSome then [] else [goal])

example (a b : Nat) : (a + 0) * 1 + (b - b) + 0 * (a * 0) = a := by
  nat_norm

/-- `succ_to_add`: change the first `Nat.succ n` in the target into the defeq `n + 1`. -/
elab "succ_to_add" : tactic => withMainContext do
  let goal ← getMainGoal
  for case (`(expr| Nat.succ ?n), ctx) in subterms (← getMainTarget) do
    replaceMainGoal [← goal.replaceTargetDefEq (ctx.fill (← `(expr| ($n : Nat) + 1)))]
    return
  throwError "succ_to_add: no `Nat.succ` found"

example (n : Nat) : Nat.succ n = n + 1 := by
  succ_to_add
  guard_target =ₛ n + 1 = n + 1
  rfl

/-- `split_bool_match`: case on the first Boolean `match` discriminant that is a local. -/
elab "split_bool_match" : tactic => withMainContext do
  for case (`(expr/reducible| (?b : Bool)), _) in matchDiscriminants (← getMainTarget) do
    if b.isFVar then
      let subgoals ← (← getMainGoal).cases b.fvarId!
      replaceMainGoal (subgoals.map (·.mvarId)).toList
      return
  throwError "split_bool_match: no Boolean discriminant"

example (b : Bool) : (match b with | true => 2 | false => 1 + 1) = 2 := by
  split_bool_match <;> rfl

/-- `and_skeleton`: refine `⊢ a ∧ b` with `And.intro ?l ?r`; the two holes become new goals. -/
elab "and_skeleton" : tactic => withMainContext do
  let goal ← getMainGoal
  let `(expr| ?a ∧ ?b) ← getMainTarget | throwError "and_skeleton: not a conjunction"
  let pf ← `(expr| (And.intro ?l ?r : $a ∧ $b))
  goal.assign pf
  replaceMainGoal (← getMVarsNoDelayed pf).toList

example (p q : Prop) (hp : p) (hq : q) : p ∧ q := by
  and_skeleton
  · exact hp
  · exact hq

/-! ## Choosing a matching relation -/

abbrev double (n : Nat) : Nat := n + n
def triple (n : Nat) : Nat := n + n + n
/-- A non-canonical, but defeq, `Add Nat` instance. -/
@[reducible] def addNat' : Add Nat := ⟨Nat.add⟩

/-- Which relations recognize `e` as "some number added to itself"? -/
def selfAddUnder (e : Expr) : MetaM (List String) := do
  let mut hits := []
  if let `(expr| (?x : Nat) + $x) := e then hits := hits ++ ["structural"]
  if let `(expr +inst| (?x : Nat) + $x) := e then hits := hits ++ ["+inst"]
  if let `(expr +beta +zeta| (?x : Nat) + $x) := e then hits := hits ++ ["+beta +zeta"]
  if let `(expr/reducible| (?x : Nat) + $x) := e then hits := hits ++ ["reducible"]
  if let `(expr/structural[+triple]| (?x : Nat) + $x + ?_) := e then hits := hits ++ ["[+triple]"]
  match (modulo := defeq) e with
  | `(expr| (?x : Nat) + $x + _) => hits := hits ++ ["defeq"]
  | _ => pure ()
  return hits

/--
info: x + x: [structural, +inst, +beta +zeta, reducible]
x +[addNat'] x: [+inst, reducible]
let y := x; (fun z => z + z) y: [+beta +zeta, reducible]
double x: [reducible]
triple x: [[+triple], defeq]
-/
#guard_msgs in
run_meta withLocalDeclD `x (mkConst ``Nat) fun x => do
  let nat := mkConst ``Nat
  let addVia := mkApp4 (mkConst ``HAdd.hAdd [0, 0, 0]) nat nat nat
    (mkApp2 (mkConst ``instHAdd [0]) nat (mkConst ``addNat'))
  let betaZeta := .letE `y nat x
    (.app (.lam `z nat (mkNatAdd (.bvar 0) (.bvar 0)) .default) (.bvar 0)) false
  let mut out := #[]
  for (name, e) in [("x + x", mkNatAdd x x), ("x +[addNat'] x", mkApp2 addVia x x),
      ("let y := x; (fun z => z + z) y", betaZeta), ("double x", mkApp (mkConst ``double) x),
      ("triple x", mkApp (mkConst ``triple) x)] do
    out := out.push s!"{name}: {← selfAddUnder e}"
  logInfo ("\n".intercalate out.toList)

end ExprQuotRewriting

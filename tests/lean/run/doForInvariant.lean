import Lean
import Std.Tactic.Do

open Lean Parser Meta Elab Do

set_option linter.unusedVariables false
set_option backward.do.legacy false

/-!
Hypothetical intrinsic invariant syntax support:
-/

@[inline]
def ForIn.forInInv {m} {ρ : Type u} {α : Type v} [ForIn m ρ α] {β}
    (xs : ρ) (s : β) (f : α → β → m (ForInStep β))
    [Monad m] [inst : ForIn.{u,v,v,v} Id ρ α] {ps} [Std.Do.WP m ps] (inv : Std.Do.Invariant (inst.toList xs) β ps) : m β :=
  forIn xs s f

meta def doInvariant := leading_parser
  "invariant " >> withPosition (
    ppGroup (many1 (ppSpace >> termParser argPrec) >> unicodeSymbol " ↦" " =>" (preserveForPP := true)) >> ppSpace >> withForbidden "do" termParser)
syntax (name := doForInvariant) "for " Term.doForDecl ppSpace doInvariant "do " doSeq : doElem

elab_rules : doElem <= dec
  | `(doElem| for $x:ident in $xs invariant $cursorBinder $stateBinders* => $body do $doSeq) => do
    let call ← elabDoElem (← `(doElem| for $x:ident in $xs do $doSeq)) dec (catchExPostpone := false)
    let_expr bind@Bind.bind m instBind σ γ call k := call
      | throwError "Internal elaboration error: `for` loop did not elaborate to a call of `Bind.bind`; got {call}."
    let_expr ForIn.forIn m ρ α instForIn σ xs s f := call
      | throwError "Internal elaboration error: `for` loop bind argument did not elaborate to a call of `ForIn.forIn`; got {call}."
    call.withApp fun head args => do
    let [u, v, w, x] := head.constLevels!
      | throwError "`Foldable.foldrEta` had wrong number of levels {head.constLevels!}"
    let mi := (← read).monadInfo
    unless ← isLevelDefEq mi.u (mkLevelMax v w) do
      throwError "The universe level of the monadic result type {mi.u} was not the maximum of that of the state tuple {w} and elements {v}. Cannot elaborate invariants for this case."
    unless ← isLevelDefEq mi.v x do
      throwError "The universe level of the result type {mi.v} and that of the continuation result type {x} were different. Cannot elaborate invariants for this case."
    -- First the non-ghost arguments
    let instMonad ← Term.mkInstMVar (mkApp (mkConst ``Monad [mi.u, mi.v]) mi.m)
    let app := mkConst ``ForIn.forInInv [u, v, w, x]
    let app := mkApp5 app m ρ α instForIn σ
    let app := mkApp3 app xs s f
    -- Now the ghost arguments
    let instForIn ← Term.mkInstMVar (mkApp3 (mkConst ``ForIn [u, v, v, v]) (mkConst ``Id [v]) ρ α)
    let ps ← mkFreshExprMVar (mkConst ``Std.Do.PostShape [mi.u])
    let instWP ← Term.mkInstMVar (mkApp2 (mkConst ``Std.Do.WP [mi.u, mi.v]) (← read).monadInfo.m ps)
    let xsToList := mkApp4 (mkConst ``ForIn.toList [u, v]) ρ α instForIn xs
    let cursor := mkApp2 (mkConst ``List.Cursor [v]) α xsToList
    let assertion := mkApp (mkConst ``Std.Do.Assertion [mi.u]) ps
    let mut tuple := s
    let mut reassignments := #[]
    while !tuple.isAppOf ``PUnit.unit do
      let (var, more) ←
        if tuple.isAppOf ``Prod.mk then
          let fst := tuple.getArg! 2
          tuple := tuple.getArg! 3
          pure (fst, true)
        else
          pure (tuple, false)
      match var.fvarId? with
      | none => -- Likely the return value slot. Push a wildcard
        reassignments := reassignments.push (← `(_))
      | some fvarId =>
        let decl ← fvarId.getDecl
        let .some id := (← read).mutVars.find? (·.getId = decl.userName) | continue
        reassignments := reassignments.push id
      unless more do break
    let mutVarBinders ← Term.Quotation.mkTuple reassignments
    let cursorσ := mkApp2 (mkConst ``Prod [v, mi.u]) cursor σ
    let success ← Term.elabFun (← `(fun ($cursorBinder, $(⟨mutVarBinders⟩)) $stateBinders* => $body)) (← mkArrow cursorσ assertion)
    let inv := mkApp3 (mkConst ``Std.Do.PostCond.noThrow [mkLevelMax v mi.u]) ps cursorσ success
    let forIn := mkApp5 app instMonad instForIn ps instWP inv
    return mkApp6 bind m instBind σ γ forIn k

/--
info: (let x := 42;
  let y := 0;
  let z := 1;
  do
  let __s ←
    ForIn.forInInv [1, 2, 3] (x, y)
        (fun i __s =>
          let x := __s.fst;
          let y := __s.snd;
          let x := x + i;
          let y := y + 7;
          pure (ForInStep.yield (x, y)))
        (PostCond.noThrow fun x =>
          match x with
          | (xs, x, y) => ⌜xs.pos = 3 ∧ x = y + z⌝)
  let x : Nat := __s.fst
  let y : Nat := __s.snd
  pure (x + y + z)).run : Nat
-/
#guard_msgs (info) in
open Std.Do in
#check Id.run do
  let mut x := 42
  let mut y := 0
  let mut z := 1
  -- NB: `z` is constant in the invariant, so it will refer to the `let`.
  -- In contrast, `x` and `y` will refer to lambda bound variables from the invariant.
  for i in [1,2,3] invariant xs => ⌜xs.pos = 3 ∧ x = y + z⌝ do
    x := x + i
    y := y + 7
  return x + y + z

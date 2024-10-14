import Lean
import Simplc.Setup
import Simplc.MVarCycles

/-!
See the documentation for the `simp_lc` command.
-/

open Lean Meta

/--
The `simp_lc` command checks the simpset for critical pairs that cannot be joined by simp, has tools
to investigate a critical pair and can ignore specific pairs or whole functions. See

* `simp_lc check`: Investigates the full simp set.
* `simp_lc inspect`: Investigates one pair
* `simp_lc whitelist`: Whitelists a critical pair
* `simp_lc ignore`: Ignores one lemma
-/
syntax "simp_lc" : command

/--
The `simp_lc check` command looks at all pairs of lemmas in the simp set and tries to construct a
critical pair, i.e. an expression `e₀` that can be rewritten by either lemma to `e₁` resp. `e₂`.
It then tries to solve `e₁ = e₂`, and reports those pairs that cannot be joined.

The tactic used to join them is
```
try contradiction
try (apply Fin.elim0; assumption)
try repeat simp_all
try ((try apply Iff.of_eq); ac_rfl)
try omega -- helps with sizeOf lemmas and AC-equivalence of +
```

The command fails if there are any join-joinable critical pairs. It will offer a “Try
this”-suggestion to insert `simp_lc whitelist` commands for all of them.

With `simp_lc check root` only critical paris where both lemmas rewrite at the same position are
considered.

With `simp_lc check in Foo` only lemmas whose name has `Foo.` as a prefix are considered. The syntax
`in _root_` can be used to select lemmas in no namespace.

The option `trace.simplc` enables more verbose tracing.

The option `simplc.stderr` causes pairs to be printed on `stderr`; this can be useful to debug cases
where the command crashes lean or runs forever.
-/
syntax "simp_lc " &"check " "root"? ("in " ident+)? : command

/--
The `simp_lc inspect thm1 thm2` command looks at critical pairs fromed by `thm1`  and `thm2`, and
always causes verbose debug output.

With `simp_lc inspect thm1 thm2 by …` one can interactively try to equate the critical pair.
-/
syntax "simp_lc " &"inspect " ident ident (Parser.Term.byTactic)? : command

/--
The `simp_lc whitelist thm1 thm2` causes the `simp_lc` commands to ignore all critical pairs formed
by these two lemmas.
-/
syntax "simp_lc " &"whitelist " ident ident : command

/--
The `simp_lc ignore thm` command causes the `simp_lc` commands to ignore all critical pairs
involving `thm`. This is different from removing `thm` from the simp set as it can still be used to
join critical pairs.
-/
syntax "simp_lc " &"ignore " ident : command

-- remove with https://github.com/leanprover/lean4/pull/4362
def My.ppOrigin [Monad m] [MonadEnv m] [MonadError m] : Origin → m MessageData
  | .decl n post inv => do
    let r ← mkConstWithLevelParams n;
    match post, inv with
    | true,  true  => return m!"← {MessageData.ofConst r}"
    | true,  false => return m!"{MessageData.ofConst r}"
    | false, true  => return m!"↓ ← {MessageData.ofConst r}"
    | false, false => return m!"↓ {MessageData.ofConst r}"
  | .fvar n => return mkFVar n
  | .stx _ ref => return ref
  | .other n => return n

def withoutModifingMVarAssignmentImpl (x : MetaM α) : MetaM α := do
  let saved ← getThe Meta.State
  try
    x
  finally
    set saved
def withoutModifingMVarAssignment {m} [Monad m] [MonadControlT MetaM m] {α} (x : m α) : m α :=
  mapMetaM (fun k => withoutModifingMVarAssignmentImpl k) x


def forallInstTelescope {α} (e : Expr) (n : Nat) (k : Expr → MetaM α) : MetaM α := do
  match n with
  | 0 => k e
  | n+1 =>
    let .forallE name d b bi := e | unreachable!
    if (← isClass? d).isSome then
      if let .some inst ← trySynthInstance d then
        return ← forallInstTelescope (b.instantiate1 inst) n k

    withLocalDecl name bi d fun x => do
      forallInstTelescope (b.instantiate1 x) n k

def mvarsToContext {α} (es1 : Array Expr) (es2 : Array Expr) (k : Array Expr → Array Expr → MetaM α) : MetaM α := do
  let es2 ← es2.mapM instantiateMVars
  let s  : AbstractMVars.State := { mctx := (← getMCtx), lctx := (← getLCtx), ngen := (← getNGen), abstractLevels := false }
  let (es2, s) := Id.run <| StateT.run (s := s) do
    es1.forM fun e => do let _ ← AbstractMVars.abstractExprMVars e
    es2.mapM fun e => AbstractMVars.abstractExprMVars e
  setNGen s.ngen
  setMCtx s.mctx
  withLCtx s.lctx (← getLocalInstances) do
    k s.fvars es2

structure CriticalPair where
  thm1 : SimpTheorem
  thm2 : SimpTheorem
  path : List Nat

def CriticalPair.pp (cp : CriticalPair) : MetaM MessageData :=
  return m!"{← My.ppOrigin cp.thm1.origin} {← My.ppOrigin cp.thm2.origin} (at {cp.path})"

abbrev M := StateT (Array CriticalPair) (StateT Nat MetaM)

def M.run (a : M α) : MetaM ((α × Array CriticalPair) × Nat):= StateT.run (StateT.run a #[]) 0

open Elab Tactic
partial
def checkSimpLC (root_only : Bool) (tac? : Option (TSyntax `Lean.Parser.Tactic.tacticSeq))
    (thm1 : SimpTheorem) (thms : SimpTheorems) : M Unit :=
  withConfig (fun c => { c with etaStruct := .none }) do
  withCurrHeartbeats do
  let val1 ← thm1.getValue
  let type1 ← inferType val1
  let (hyps1, _bis, eq1) ← forallMetaTelescopeReducing type1
  let eq1 ← whnf (← instantiateMVars eq1)
  let some (_, lhs1, rhs1) := eq1.eq?
    | return -- logError m!"Expected equality in conclusion of {thm1}:{indentExpr eq1}"

  let (rewritten, Expr.mvar goal) ← Conv.mkConvGoalFor lhs1 | unreachable!
  -- logInfo m!"Initial goal: {goal}"

  let rec go (path : List Nat) (cgoal : MVarId) : M Unit := do
    let (t, _) ← Lean.Elab.Tactic.Conv.getLhsRhsCore cgoal
    if t.isMVar then
      -- logInfo m!"Ignoring metavariable {t} (kind: {repr (← t.mvarId!.getKind)})"
      return

    let matchs := (← thms.pre.getUnify t simpDtConfig) ++ (← thms.post.getUnify t simpDtConfig)
    for thm2 in matchs do
      let critPair : CriticalPair := ⟨thm1, thm2, path⟩
      if thms.erased.contains thm2.origin then continue
      if (← isCriticalPairWhitelisted (thm1.origin.key, thm2.origin.key)) then continue
      if path.isEmpty then
        unless thm1.origin.key.quickLt thm2.origin.key do continue
      modifyThe Nat Nat.succ
      let good ← withoutModifingMVarAssignment do withCurrHeartbeats do
        if simplc.stderr.get (← getOptions) then
          IO.eprintln s!"{thm1.origin.key} {thm2.origin.key}"
        withTraceNode `simplc (do return m!"{exceptBoolEmoji ·} {← critPair.pp}") do
          let val2  ← thm2.getValue
          let type2 ← inferType val2
          let (hyps2, _bis, type2) ← forallMetaTelescopeReducing type2
          let type2 ← whnf (← instantiateMVars type2)
          let type1 ← cgoal.getType
          if ← withReducible (isDefEq type1 type2) then
            MVarCycles.checkMVarsCycles -- may not be needed anymore with https://github.com/leanprover/lean4/pull/4420
            cgoal.assign (val2.beta hyps2) -- TODO: Do we need this, or is the defeq enough?

            mvarsToContext (hyps1 ++ hyps2) #[lhs1, rhs1, rewritten] fun _fvars r => do
              let #[cp, e1, e2] := r | unreachable!
              -- Do we need forallInstTelescope here?
              -- At some point I was using
              -- forallInstTelescope (← mkForallFVars fvars goal) fvars.size fun goal => do
              -- here
              trace[simplc]
                m!"Expression{indentExpr cp}\n" ++
                m!"reduces with {← My.ppOrigin thm1.origin} to{indentExpr e1}\n" ++
                m!"and     with {← My.ppOrigin thm2.origin} to{indentExpr e2}\n"

              let goal ← mkEq e1 e2
              check goal
              let .mvar simp_goal ← mkFreshExprSyntheticOpaqueMVar goal
                | unreachable!
              let (_, simp_goal) ← simp_goal.intros
              check (mkMVar simp_goal)
              let (remaining_goals, _) ← simp_goal.withContext do
                match tac? with
                | .some tac => runTactic simp_goal tac
                | .none =>
                  runTactic simp_goal (← `(tactic|(
                    try contradiction
                    try (apply Fin.elim0; assumption)
                    try repeat simp_all
                    try ((try apply Iff.of_eq); ac_rfl)
                    try omega -- helps with sizeOf lemmas and AC-equivalence of +
                    try (congr; done)
                    try apply Subsingleton.elim
                  )))
              if remaining_goals.isEmpty then
                return true
              trace[simplc] m!"Joining failed with\n{goalsToMessageData remaining_goals}"
              return false
            else
              trace[simplc] m!"Not a critical pair, discrTree false positive:" ++
                m!"{indentExpr type1.consumeMData}\n=!={indentExpr type2}"
              return true
      unless good do
        modify (·.push critPair)

    unless root_only do
      if true then
        -- The following works, but sometimes `congr` complains
        if t.isApp then do
          let goals ←
            try Lean.Elab.Tactic.Conv.congr cgoal
            catch e =>
              trace[simplc] m!"congr failed on {cgoal}:\n{← nestedExceptionToMessageData e}"
              pure []
          let goals := goals.filterMap id
          for hi : i in [:goals.length] do
            if (← goals[i].getType).isEq then
              withoutModifingMVarAssignment $ do
                -- rfl all othe others, akin to `selectIdx`
                for hj : j in [:goals.length] do
                  if i ≠ j then
                    if (← goals[j].getType).isEq then
                      goals[j].refl
                    else
                      -- Likely a subsingleton instance, also see https://github.com/leanprover/lean4/issues/4394
                      -- just leave in place, will become a parameter
                      pure ()
              go (path ++ [i+1]) goals[i]
      else
        -- This should be simpler, but does not work, (the
        -- isDefEqGuarded above fails) and I do not see why
        if let .app f x := t then
          if (←inferType f).isArrow then
            withoutModifingMVarAssignment do
              let (rhs, subgoal) ← Conv.mkConvGoalFor x
              rhs.mvarId!.setKind .natural
              goal.assign (← mkCongrArg f subgoal)
              go (path ++ [2]) subgoal.mvarId!
          -- else logInfo m!"Cannot descend into dependent {f} in {t}"
          withoutModifingMVarAssignment do
            let (rhs, subgoal) ← Conv.mkConvGoalFor f
            rhs.mvarId!.setKind .natural
            goal.assign (← mkCongrFun subgoal x)
            go (path ++ [1]) subgoal.mvarId!
  go [] goal

def mkSimpTheorems (name : Name) : MetaM SimpTheorems := do
  let sthms : SimpTheorems := {}
  sthms.addConst name

def mkSimpTheorem (name : Name) : MetaM SimpTheorem := do
  let sthms ← mkSimpTheorems name
  let sthms := sthms.pre.values ++ sthms.post.values
  return sthms[0]!

def delabInspectCmd (cp : CriticalPair) : MetaM (TSyntax `command) := do
  `(command|simp_lc inspect $(mkIdent cp.thm1.origin.key) $(mkIdent cp.thm2.origin.key))

def reportBadPairs  (cmdStx? : Option (TSyntax `command)) (act : M Unit) (stats := false) : MetaM Unit := do
  let ((.unit, badPairs), numPairs) ← M.run act
  if stats then
    logInfo m!"Investigated {numPairs} critical pairs"
  unless badPairs.isEmpty do
    logError <| m!"Found {badPairs.size} non-confluent critical pairs:" ++
      indentD (.joinSep ((← badPairs.mapM (·.pp)).toList) "\n")
    if let .some cmdStx := cmdStx? then
      let mut str : String := ""
      for cp in badPairs do
        let stx ← delabInspectCmd cp
        str := str ++ "\n" ++ (← PrettyPrinter.ppCategory `command stx).pretty
      str := str ++ "\n" ++ (← PrettyPrinter.ppCategory `command cmdStx).pretty
      TryThis.addSuggestion cmdStx { suggestion := str, messageData? := m!"(lots of simp_lc_inspect lines)" }

def checkSimpLCAll (cmdStx : TSyntax `command) (root_only : Bool) (pfixs? : Option (Array Name)) : MetaM Unit := do
  let sthms ← getSimpTheorems
  let thms := sthms.pre.values ++ sthms.post.values
  let thms ← thms.filterM fun sthm => do
    if sthms.erased.contains sthm.origin then
      return false
    if let .decl n _ false := sthm.origin then
      if (← isIgnoredName n) then
        return false
      if let some pfixs := pfixs? then
        return pfixs.any fun pfix =>
          if pfix = `_root_
          then n.components.length = 1
          else pfix.isPrefixOf n
      return true
    return false
  logInfo m!"Checking {thms.size} simp lemmas for critical pairs"
  let filtered_sthms := thms.foldl Lean.Meta.addSimpTheoremEntry (init := {})
  -- logInfo m!"{names}"
  -- let thms := thms[:104] ++ thms[105:]
  reportBadPairs (stats := true) cmdStx do
    for thm1 in thms do
      try
        checkSimpLC root_only .none thm1 filtered_sthms
      catch e => logError m!"Failed to check {← My.ppOrigin thm1.origin}\n{← nestedExceptionToMessageData e}"

def warnIfNotSimp (n : Name) : CoreM Unit := do
  try
    _ ← (← getSimpTheorems).erase (.decl n)
  catch e =>
    logWarning e.toMessageData

def whiteListCriticalPair (cmdStx : Syntax) : NamePair → MetaM Unit := fun ⟨name1, name2⟩ => do
  warnIfNotSimp name1
  warnIfNotSimp name2
  if simplc.checkWhitelist.get (← getOptions) then
    let sthms : SimpTheorems ← SimpTheorems.addConst {} name2
    let ((.unit, badPairs), _) ← M.run do
      checkSimpLC false none (← mkSimpTheorem name1) sthms
    if badPairs.isEmpty then
      logWarning "No non-confluence detected. Maybe remove this?"
      TryThis.addSuggestion cmdStx { suggestion := "", messageData? := m!"(remove this command)" }
  let pair := if name2.quickLt name1 then (name2, name1) else (name1, name2)
  modifyEnv (simpLCWhitelistExt.addEntry · pair)

open Elab Command
elab_rules : command
| `(command|simp_lc inspect $ident1:ident $ident2:ident $[by $tac?]?) => liftTermElabM fun _ => do
  let name1 ← realizeGlobalConstNoOverloadWithInfo ident1
  let name2 ← realizeGlobalConstNoOverloadWithInfo ident2
  let sthms : SimpTheorems ← SimpTheorems.addConst {} name2
  withOptions (·.setBool `trace.simplc true) do reportBadPairs .none do
    checkSimpLC false tac? (← mkSimpTheorem name1) sthms

| `(command|simp_lc check $[root%$root?]? $[in $[$pfixs]*]?) => liftTermElabM do
  let stx ← getRef
  let pfixs := pfixs.map (·.map (·.getId))
  checkSimpLCAll ⟨stx⟩ root?.isSome pfixs

| `(command|simp_lc whitelist $thm1 $thm2) => liftTermElabM do
  let stx ← getRef
  let name1 ← realizeGlobalConstNoOverloadWithInfo thm1
  let name2 ← realizeGlobalConstNoOverloadWithInfo thm2
  whiteListCriticalPair stx (name1, name2)

| `(command|simp_lc ignore $thm) => liftTermElabM do
  ignoreName (← realizeGlobalConstNoOverloadWithInfo thm)

| `(command|simp_lc) => liftTermElabM do
  logWarning m!"Please use one of the `simp_lc` subcommands."

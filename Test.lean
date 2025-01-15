import Lean
open Lean
open Lean.Parser
open Lean.Elab.Command
open Lean.Elab
open Lean.Elab.Tactic
open Lean.Meta
open Lean.SubExpr

def SatisfiesM {m : Type u → Type v} {α} [Functor m] (p : α → Prop) (x : m α) : Prop :=
  ∃ x' : m {a // p a}, Subtype.val <$> x' = x

-- this is actually the fwd direction of SatisfiesM_Id_eq. Good!
theorem Id.run_satisfies2 : SatisfiesM P x → P (Id.run x) := by
  rintro ⟨y, eq⟩
  exact (eq ▸ y.property)

/-- `SatisfiesM` distributes over `pure`, general version / weakest precondition version. -/
protected theorem SatisfiesM.pure [Applicative m] [LawfulApplicative m]
    (h : p a) : SatisfiesM (m := m) p (pure a) := ⟨pure ⟨_, h⟩, by simp⟩

/-- `SatisfiesM` distributes over `>>=`, general version. -/
protected theorem SatisfiesM.bind [Monad m] [LawfulMonad m] {f : α → m β}
    (hx : SatisfiesM p x) (hf : ∀ a, p a → SatisfiesM q (f a)) :
    SatisfiesM q (x >>= f) := by
  match x, hx with | _, ⟨x, rfl⟩ => ?_
  have g a ha := Classical.indefiniteDescription _ (hf a ha)
  refine ⟨x >>= fun ⟨a, h⟩ => g a h, ?_⟩
  simp [← bind_pure_comp]; congr; funext ⟨a, h⟩; simp [← (g a h).2, ← bind_pure_comp]

/-- `SatisfiesM` distributes over `>>=`, weakest precondition version. -/
protected theorem SatisfiesM.bind_pre [Monad m] [LawfulMonad m] {f : α → m β}
    (hx : SatisfiesM (fun a => SatisfiesM q (f a)) x) :
    SatisfiesM q (x >>= f) := hx.bind fun _ h => h

/-- `SatisfiesM` distributes over `>>=`, weakest precondition version. -/
protected theorem SatisfiesM.bind_pre2 [Monad m] [LawfulMonad m] {f : α → m β}
    (hx : SatisfiesM (fun a => SatisfiesM q (f a)) x) :
    SatisfiesM q (x >>= f) := hx.bind fun _ h => h

elab "wlp" /-("invariant " ilbls:ident ": " inv:term)*-/ : tactic => withMainContext <| do
  let mut verification_conds := #[]
  while true do
    let goal :: goals ← getGoals | break
    if ← goal.isAssigned then setGoals goals; continue
    let ty ← instantiateMVars (← goal.getType)
    -- ty = @SatisfiesM α m [Functor m] (post : α → Prop) (prog : m α)
    if ¬(ty.isAppOfArity `SatisfiesM 5) then
      logInfo m!"give up on {ty}"
      verification_conds := verification_conds.push goal
      setGoals goals
      continue
    let prog := ty.appArg!

    -- Convention: ⟦P⟧(x) for SatisfiesM P x
    if prog.isAppOfArity `Pure.pure 4 then
      -- prog = @pure m [Pure m] α (x : α)
      -- ⟦P⟧(pure x)
      -- <=={Satisfies.pure}
      -- P x
      let [goal] ← goal.applyConst ``SatisfiesM.pure | throwError "argh"
      replaceMainGoal [goal]
      continue
    else if prog.isAppOfArity `Bind.bind 6 then
      -- prog = @bind m [Bind m] α β e f
      -- ⟦P⟧(bind e f)
      -- <=={Satisfies.bind_pre}
      -- P⟦fun r => ⟦P⟧(f r)⟧(e)
      let [goal] ← goal.applyConst ``SatisfiesM.bind_pre | throwError "argh"
      replaceMainGoal [goal]
      continue
    else if prog.isLet then
      -- C ⊢ ⟦P⟧(do let x : ty := val; prog)
      -- <=={lift_let; intros}
      -- C; let x : ty := val ⊢ ⟦P⟧(prog)
      let ty ← instantiateMVars (← goal.getType)
      let goal ← goal.change (← ty.liftLets mkLetFVars)
      let (_xs, goal) ← goal.intros
      replaceMainGoal [goal]
      continue
    else if prog.isIte then
      -- ⟦P⟧((if b then prog₁ else prog₂))
      -- <=={split}
      -- (b → ⟦P⟧(prog₁) ∧ ((¬b) → ⟦P⟧(prog₂))
      let some (tt,ff) ← splitIfTarget? goal | throwError "wlp failed"
      replaceMainGoal [tt.mvarId, ff.mvarId]
      continue
    else if let .fvar fvarId := prog.getAppFn then -- inline locals
      -- C; let __do_jp : ty := val ⊢ ⟦P⟧(__do_jp y x))
      -- <=={dsimp only [__do_jp]}
      -- C; let __do_jp : ty := val ⊢ ⟦P⟧(val y x))
      try
        -- Why can't I test fvarId.isLetVar? here, but zeta succeeds???
        let goal ← zetaDeltaTarget goal fvarId
        replaceMainGoal [goal]
        continue
      catch _ => pure ()

    logInfo m!"give up on {prog}"
    verification_conds := verification_conds.push goal
    setGoals goals
    continue

  setGoals verification_conds.toList


theorem test_1 : SatisfiesM (m:=Id) (fun r => r = 3) (do return 3) := by
  wlp
  trivial

theorem test_2 : SatisfiesM (m:=Id) (fun r => r = id 3) (do let mut id := 5; id := 3; return id) := by
  wlp
  trivial

theorem test_3 (h : SatisfiesM (fun _ => SatisfiesM (m:=Id) P (do e₂; e₃)) e₁) : SatisfiesM (m:=Id) P (do e₁; e₂; e₃) := by
  wlp
  trivial

theorem test_4 : SatisfiesM (m:=Id) (fun r => r ≤ 1) (do let mut x := 5; if x > 1 then { x := 1 } else { x := x }; pure x) := by
  wlp
  omega
  simp [gt_iff_lt, Nat.le_of_not_gt] at *
  assumption


/-
https://lean-fro.zulipchat.com/#narrow/channel/398861-general/topic/baby.20steps.20towards.20monadic.20verification

-/



#check wp⟦let x ← pure 3; pure x⟧(fun r => r = 15)
/-

goal : Q (impl n)
       Q (Id.run (do impl' n))
       SatisfiesM Q (do impl' n)

Wenn
  wlp(s,P)
Dann
  SatisfiesM P (do s)

Why do we need explicit σ instead of "substituting"?
For one, what do we do with loop invariants, where there is not a single definition?
Or the postcondition after an if-diamond?
"Substitution" only makes sense in an SSA world.
Hence any predicate depends on a tuple σ;

P : σ × α → Prop
(in general, both σ and α are indices)

Q: Is σ the actual state or rather a syntax, i.e., a var to Syntax mapping? I think the latter!
And ofc., P is also a function constructing syntax for a predicate.
So it's rather

def Subst := (Name ↦ Syntax Var) -- Name to SSA val
def Pred := Subst → (Syntax (α → Prop))

wp : Syntax Cmd × Pred → Pred
wp(do return $e, P) σ := `(SatisfiesM.pure ($(P σ) $e))
wp(do lift $e, P) σ := `(satisfying $(P σ) $e)
wp(do let mut $x := $e; $s, P) σ := `(let v := $e; let $x := v; $(wp((do $s), P) σ[x := `v]))
wp(do $x := $e, P) σ := `(let v := $e; $(P σ[x := `v]) ())
wp(do let $x ← $s₁; $s₂, P) σ := wp(s₁, fun σ' => `(fun r => let $x := r; let $σ'; $(wp(s₂, P) σ'))) σ
wp(do if $b then $s₁ else s₂, P) σ := `(($b = true → $(wlp(s₁, P) σ)) ∧ ($b = false → $wlp(s₂, P) σ))
wlp(do while $b do $s invariant $Pinv, $P) σ := (abstract $Pinv over names in σ, call that $Pinv)
                                                `(  $b = true  ∧ $(Pinv σ) → $(wlp(s,Pinv σ))
                                                  ∧ $b = false ∧ $(Pinv σ) → $(P σ))

-/


abbrev Subst := Std.HashMap Name (TSyntax `term) -- Name to SSA value
#check Lean.Parser.Term.doSeq

private def Lean.Syntax.getDoSeqElems (doSeq : Syntax) : List Syntax :=
  if doSeq.getKind == ``Parser.Term.doSeqBracketed then
    doSeq[1].getArgs.toList.map fun arg => arg[0]
  else if doSeq.getKind == ``Parser.Term.doSeqIndent then
    doSeq[0].getArgs.toList.map fun arg => arg[0]
  else
    []

def restore (σ : Subst) (rest : MacroM (TSyntax `term)) : MacroM (TSyntax `term) := do
  let mut r ← rest
  for (x, v) in σ.toList do
    r ← `(let $(mkIdent x) := $(v); $r)
  return r

def tupelize (σ : Subst) : MacroM (TSyntax `term) := do
  let mut r ← `(())
  for (_x, v) in σ.toList do
    r ← `(($(v), $r))
  return r

mutual
  partial def wp (seq : TSyntax `Lean.Parser.Term.doSeq) (P : Subst → MacroM (TSyntax `term)) : Subst → MacroM (TSyntax `term) :=
    List.foldr (wp_one ∘ TSyntax.mk) P seq.raw.getDoSeqElems
  partial def wp_one (syn : TSyntax `doElem) (P : Subst → MacroM (TSyntax `term)) (σ : Subst) : MacroM (TSyntax `term) := restore σ <| do match syn with
  -- | `(doElem|return $e) => fun P σ => do `(SatisfiesM (m:=Id) $(← P σ) (pure $e))
  | `(doElem|$e:term) => do `(SatisfiesM (m:=Id) $(← P σ) $e)
  | `(doElem|let mut $x:ident := $e) => do `(let v := $e; $(← P (σ.insert x.raw.getId (← `(v)))))
  | `(doElem|$x:ident := $e) => do `(let v := $e; $(← P (σ.insert x.raw.getId (← `(v)))))
  | `(doElem|let $x:ident ← $s) => wp_one s (fun σ' => do `(fun $x => $(← P (σ'.erase x.raw.getId)))) σ
  | `(doElem|if $b then $s₁ else $s₂) => do `(($b → $(← wp s₁ P σ)) ∧ (¬$b → $(← wp s₂ P σ)))
  | `(doElem|while $b do $s) => do `(fun Pinv => ($b ∧ Pinv $(← tupelize σ) → $(← wp s (fun σ' => do `(fun _r => Pinv $(← tupelize σ'))) σ)) ∧ (fun r => ¬$b ∧ Pinv $(← tupelize σ) → $(← P σ) r))
  | _ => Lean.Macro.throwUnsupported
end

/-
Alternatives:
1. Hook into do elaboration; compute wp from syntax, persist wp+proof of soundness in .olean.
   Pro: Simple, intuitive impl.
   Con: even just wp can be larger than actual code => code bloat
2. Compute wp from Core Expr.
-/

macro "wp⟦" s:doSeq "⟧(" P:term ")"   : term => wp s (fun _σ => pure P) Std.HashMap.empty

#check wp⟦pure 15⟧(fun r => r = 15)
#check wp⟦let x ← pure 3; pure x⟧(fun r => r = 15)
#check wp⟦let mut x := 3; pure x⟧(fun r => r = 15)
#check wp⟦let mut x := 5; if x > 1 then { x := 1 } else { x := x }; pure x⟧(fun r => r = 15)
#check wp⟦let mut x := 5; while x > 1 do { x := x - 1 }; pure x⟧(fun r => r = 15)

theorem blah : wp⟦pure 15⟧(P) → SatisfiesM (m:=Id) P (do return 15) := fun h => h
theorem blah1 : wp⟦let x ← pure 3; pure x⟧(P) → SatisfiesM (m:=Id) P (do let x ← pure 3; pure x) := by
  rintro ⟨⟨x, ⟨⟨x₂,h₂⟩, h₁⟩⟩, h⟩
  simp only [Id.pure_eq, Id.bind_eq, Id.map_eq] at h₁ h ⊢
  simp_all
  exact SatisfiesM.pure h₂
theorem blah2 : wp⟦let mut x := 5; if x > 1 then { x := 1 } else { x := x }; pure x⟧(P)
              → SatisfiesM (m:=Id) P (do let mut x := 5; if x > 1 then { x := 1 } else { x := x }; pure x) := by
  simp [Nat.reduceLT]

#check CommandElabM
#eval format <$> liftMacroM (do wp (← `(doSeq|return 15)) (fun σ => `(fun r => r = 15)) Std.HashMap.empty)

-- syntax "wp⟦" doSeq "⟧" : term
-- macro_rules
-- | `(wp⟦do return $e⟧) => fun P σ => do `(SatisfiesM.pure ($(← P σ) $e))
-- | `(wp⟦do $e:term⟧) => fun P σ => do `(SatisfiesM.satisfying $(← P σ) $e)
-- | `(wp⟦do let mut $x := $e; $s⟧) => fun P σ => do `(let v := $e; let $x := v; wp⟦do $s⟧)



/-
Wenn
  P
Dann
  SatisfiesM sp(P,s) (do s)

{P}

{P1 * P2(mut vars)} return e {fun ρ σ => Q}

Wenn {P} cmd {v. Q}
Dann Id.run
Id.run ()

P (do <fib_impl>)
...
P (do return x)


def bar (n : Nat) := Id.run do

  let mut i := 0
  while i < n do
    i := i + 1
  return i

theorem bar_upper_bound : bar n = n := by
  unfold bar
  mut_intro i
  while_inv fun i =>

def foo (xs : List Nat) := Id.run do
  let mut s := 0
  for x in xs do
    if x % 2 = 0 then
      continue
    if x > 5 then
      break
    s := s + x
  return s

theorem foo_upper_bound : foo xs ≤ xs.length * 5 := by
  unfold foo
  mut_intro s
  for_inv x in xs (h : s ≤ xs.old.length * 5)
  simp

def fib_spec : Nat → Nat
| 0 => 0
| 1 => 1
| n+2 => fib_spec n + fib_spec (n+1)

theorem fib_spec_rec (h : n > 1) : fib_spec n = fib_spec (n-2) + fib_spec (n-1) := by
  rw (occs := .pos [1]) [fib_spec.eq_def]
  split
  repeat omega
  --omega
  simp

def fib_impl (n : Nat) := Id.run do
  if n = 0 then return 0
  let mut i := 1
  let mut a := 0
  let mut b := 0
  b := b + 1
  while@first_loop i < n do
    let a' := a
    a := b
    b := a' + b
    i := i + 1
    if n > 15 then return 42
  return b

theorem blah : let i := 1; ¬(n = 0) → i ≤ n := by intro _ h; have : _ := Nat.succ_le_of_lt (Nat.zero_lt_of_ne_zero h); assumption

theorem fib_correct : fib_impl n = fib_spec n := by
  unfold fib_impl
  split -- if_split n = 0
  case isTrue  h => simp[h, fib_spec]; exact (Id.pure_eq 0)
  case isFalse h =>
  let_mut_intro i a b' -- i = 1, a = 0, b' = 0.
  let_mut_upd b        -- b = b' + 1
  while_inv (1 ≤ i ∧ i ≤ n ∧ a = fib_spec (i-1) ∧ b = fib_spec i)
  case base => by
    -- goal: show invariant
    -- (weirdness: hcond and hind are not in scope here!
    rw[Nat.sub_self, fib_spec, fib_spec]; sorry
  case induct hcond hinv => by
    -- hcond : i < n
    -- hinv : ...
    -- goal: new(hinv). Q: How do we display this in the goal view?
    let_intro a' ha'  -- ha' : a' = a.     Very similar to intro?
    let_mut_upd a ha  -- ha : a = b         (a' = a†, hcond = ..., hinv = ...)
    let_mut_upd b hb  -- hb : b = a' + b†   (a = b†, ...)
    let_mut_upd i hi  -- hi : i = i† + 1
    -- Now:
    -- hcond : i† < n
    -- hinv : 1 ≤ i† ∧ i ≤ n ∧ a† = fib_spec (i†-1) ∧ b† = fib_spec i†
    have hi1 : i > 1              := by ... hi ... hinv ...
    have     : i ≤ n              := by ... hi ... hinv ...
    have     : a = fib_spec (i-1) := by rw[ha, hinv, hi]
    have     : b = fib_spec i     := by rw[hb, ha', hinv, hinv, (fib_spec_rec hi1).symm]
    show 1 ≤ i ∧ i ≤ n ∧ a = fib_spec (i-1) ∧ b = fib_spec i
    by ⟨by simp_arith[hi1], by assumption, by assumption, by assumption⟩
  intro (hafter : ¬(i < n))
  intro (hinv : ...)
  have i = n          := by simp[hinv, hafter]
  have b = fib_spec n := by simp[this, hinv]
  return_post this

theorem fib_correct_david : fib_impl n = fib_spec n := by
  unfold fib_impl
  do =>
    if n = 0 then by simp[h, fib_spec]
    let mut i a b'
    b := _
    while hcond -- : i < n
          (n - i)
          (hinv : 1 ≤ i ∧ i ≤ n ∧ a = fib_spec (i-1) ∧ b = fib_spec i)
          (by grind ... /- show inv in base case; hinv not in scope here... -/) do
      let a'
      assume a = b;
      a := _
      ----

      ---
      b := _
      i := _
      continue (by ... : 1 ≤ i ∧ i ≤ n ∧ a = fib_spec (i-1) ∧ b = fib_spec i)  /- show inv in inductive case, using old(hinv) and hcond -/)
    return (by ... : b = fib_spec n)

def fib_correct_wlp  : fib_impl n = fib_spec n := Id.run_satisfies2 by
  wlp
    termination first_loop: ...
    invariant   first_loop: 1 ≤ i ∧ i ≤ n ∧ a = fib_spec (i-1) ∧ b = fib_spec i
    by
      /- X goals -/
      grind

def fib_impl_intrinsic (n : Nat) := Id.run do
  if n = 0 then return 0
  let mut i := 1
  let mut a := 0
  let mut b := 0
  b := b + 1
  while i < n
    invariant 1 ≤ i
    invariant i ≤ n
    invariant a = fib_spec (i-1)
    invariant b = fib_spec i
    do
    let a' := a
    a := b
    b := a' + b
    i := i + 1
  return b
-/

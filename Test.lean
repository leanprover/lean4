import Lean
open Lean
open Lean.Parser
open Lean.Elab.Command
open Lean.Elab
open Lean.Elab.Tactic
open Lean.Meta
open Lean.SubExpr
--open Std.Range

def PredTransM α := (α → Prop) → Prop
instance : Monad PredTransM where
  pure x := fun p => p x
  bind x f := fun p => x (fun a => f a p)
instance : LawfulMonad PredTransM := sorry


/-- Backward predicate transformer derived from a substitution property of monads.
A generic effect observation that can be used to observe all monads.
It is oblivious to any computations that happened before it, so `Obs.bind` loses information
for non-pure monads.
It is a suitable choice for the base layer of a specification monad stack if
the observation does the right thing for your use case; see the equivalence lemmas such as
`Obs_Id_eq`.
More sophisticated observations can be built on top of `Obs` by wrapping suitable monad transformers such
as `StateT` or `ExceptT`.
-/
def Obs {m : Type u → Type v} {α} [Monad m] (x : m α) : PredTransM α := fun p =>
  ∀ {β} {f g : α → m β}, (∀ a, p a → f a = g a) → x >>= f = x >>= g

notation "obs⟦" x "⟧" => Obs x

theorem Obs.pure [Monad m] [LawfulMonad m]
    (h : p a) : obs⟦pure (f:=m) a⟧ p := by
  simp_all only [Obs, pure_bind, implies_true]

--set_option pp.all true in
--theorem repro {m : Type u → Type v} {p : α × σ → Prop} [Monad m] [LawfulMonad m] (hp : p (a, s)) :
--  (do Obs (m := StateT σ m) (set s); Obs (m := StateT σ m) (Pure.pure (a, s))) p
--  = Obs (m := StateT σ m) (set s) (fun _ => True)
--  := by
--    replace hp : Obs (m := StateT σ m) (Pure.pure (a, s)) p := (Obs.pure hp)
--    set_option trace.Tactic.rewrites true in
--    conv => lhs; arg 1; intro; rw [eq_true @hp]

theorem Obs.bind [Monad m] [LawfulMonad m] {f : α → m β}
    (hx : obs⟦x⟧ (fun a => obs⟦f a⟧ q)) :
    obs⟦x >>= f⟧ q := by
  intros γ f g hfg
  simp only [bind_assoc]
  exact hx fun a hq => hq hfg

theorem Obs.subst [Monad m] [LawfulMonad m] {x : m α}
  (hp : obs⟦x⟧ p) (hf : ∀ a, p a → f a = g a) : x >>= f = x >>= g := hp hf

theorem Obs.subst_pre [Monad m] [LawfulMonad m] {x : m α} (hp : obs⟦x⟧ (fun r => f r = g r)) :
  x >>= f = x >>= g := by apply hp; simp

theorem Obs.conj [Monad m] [LawfulMonad m] {x : m α}
    (hp : obs⟦x⟧ p) (hq : obs⟦x⟧ q) : obs⟦x⟧ (fun r => p r ∧ q r) := by
  intros β f g hfg
  open Classical in
  calc x >>= f
    _ = x >>= (fun r => if p r ∧ q r then f r else f r) := by simp
    _ = x >>= (fun r => if p r ∧ q r then g r else f r) := by simp +contextual [hfg]
    _ = x >>= (fun r => if q r then g r else f r) := hp (by simp +contextual)
    _ = x >>= g := hq (by simp +contextual)

theorem Obs.inf_conj [Monad m] [LawfulMonad m] {x : m α}
    (hp : obs⟦x⟧ p) (hq : obs⟦x⟧ q) : obs⟦x⟧ (fun r => sInf { p ∈ ps // p r }) := by
  intros β f g hfg
  open Classical in
  calc x >>= f
    _ = x >>= (fun r => if p r ∧ q r then f r else f r) := by simp
    _ = x >>= (fun r => if p r ∧ q r then g r else f r) := by simp +contextual [hfg]
    _ = x >>= (fun r => if q r then g r else f r) := hp (by simp +contextual)
    _ = x >>= g := hq (by simp +contextual)

@[simp]
theorem Monad.bind_unit {m : Type u → Type v} [Monad m] {x : m PUnit} {f : PUnit → m α} :
  (do let a ← x; f a) = (do x; f ⟨⟩) := by simp only

theorem Obs.split_unit {m : Type u → Type v} [Monad m] {x : m PUnit} (hp : p) :
  obs⟦x⟧ (fun _ => p) := fun hfg =>
    funext (fun u => hfg u hp) ▸ rfl

def KimsObs {m : Type u → Type v} {α} [Functor m] (p : α → Prop) (x : m α) : Prop :=
  (fun r => (r, p r)) <$> x = (fun r => (r, True)) <$> x

def KimsObs_of_Obs {m : Type u → Type v} {α} [Monad m] [LawfulMonad m] (p : α → Prop) (x : m α)
  (h : obs⟦x⟧ p) : KimsObs p x := by
  unfold KimsObs
  simp [← LawfulMonad.bind_pure_comp]
  apply h
  intros
  simp [*]

@[simp]
theorem Obs_Id_eq : obs⟦x⟧ P ↔ P (Id.run x) := by
  constructor
  case mp =>
    intro h
    replace h := KimsObs_of_Obs P x h
    simp [KimsObs] at h
    injection h
    simp[*, Id.run]
  case mpr =>
    intro h; apply Obs.pure; exact h

theorem Obs.imp [Monad m] [LawfulMonad m] {p : Prop} {f : α → m β} :
    obs⟦f a⟧ (fun r => p → q r) ↔ (p → obs⟦f a⟧ q) := by
  if hp : p
  then simp_all
  else simp_all; intro _ _ _ h; simp[funext (fun a => h a ⟨⟩)]

theorem Obs.mono [Monad m] [LawfulMonad m] {x : m a}
    (h : obs⟦x⟧ p) (H : ∀ {a}, p a → q a) : obs⟦x⟧ q := by
    intro _ _ _ hfg
    apply h
    simp_all only [implies_true]

class LawfulMonadState (σ : semiOutParam (Type u)) (m : Type u → Type v) [Monad m] [LawfulMonad m] [MonadStateOf σ m] where
  get_set : (do let s ← get; set s) = pure (f := m) ⟨⟩
  set_get {k : σ → m β} : (do set s₁; let s₂ ← get; k s₂) = (do set s₁; k s₁)
  set_set {s₁ s₂ : σ} : (do set s₁; set s₂) = set (m := m) s₂

theorem LawfulMonadState.set_get_pure [Monad m] [LawfulMonad m] [MonadStateOf σ m] [LawfulMonadState σ m] {s : σ} :
  (do set s; get) = (do set (m := m) s; pure s) := by
    calc (do set s; get)
      _ = (do set s; let s' ← get; pure s') := by simp
      _ = (do set s; pure s) := by rw [LawfulMonadState.set_get]
attribute [simp] LawfulMonadState.get_set LawfulMonadState.set_get LawfulMonadState.set_set LawfulMonadState.set_get_pure

instance [Monad m] [LawfulMonad m] : LawfulMonadState σ (StateT σ m) where
  get_set := by intros; ext s; simp
  set_get := by intros; ext s; simp
  set_set := by intros; ext s; simp

def SatisfiesSM {m : Type u → Type v} {α} [Monad m] (x : StateT σ m α) (p : α × σ → Prop) : Prop :=
  obs⟦do let a ← x; let s ← get; pure (a, s)⟧ p

theorem SatisfiesSM.subst [Monad m] [LawfulMonad m] {x : StateT σ m α}
  {f g : α → StateT σ m β}
  (hp : SatisfiesSM x p) (hf : ∀ a s, p (a, s) → (do set s; f a) = (do set s; g a)) :
  x >>= f = x >>= g := by
    suffices h : (do let (a,s) ← (do let a ← x; let s ← get; pure (a, s)); set s; f a) = (do let (a,s) ← (do let a ← x; let s ← get; pure (a, s)); set s; g a) by
      simp at h
      simp[← LawfulMonad.bind_assoc] at h
      assumption
    unfold SatisfiesSM at hp
    apply hp.subst fun ⟨a, s⟩ => hf a s

theorem Obs.split_step [Monad m] [LawfulMonad m] {x : m (ForInStep β)}
    {done : β → Prop} {yield : β → Prop}
    (hyield : obs⟦x⟧ (∀ b', · = .yield b' → yield b'))
    (hdone :  obs⟦x⟧ (∀ b', · = .done b'  → done b')) :
    obs⟦x⟧ (fun | .yield b' => yield b' | .done b' => done b') := by
  apply Obs.mono (Obs.conj hyield hdone)
  rintro a ⟨hyield, hdone⟩
  split <;> solve_by_elim

theorem Obs.forIn_list
  [Monad m] [LawfulMonad m]
  {xs : List α} {init : β} {f : α → β → m (ForInStep β)}
  (inv : List α → β → Prop)                     -- user-supplied loop invariant
  (hpre : inv xs init)                          -- pre⟦for {inv} xs init f⟧(p)
  (hweaken : ∀ b, inv [] b → p b)               -- vc₁: weaken invariant to postcondition after loop exit
  (hdone : ∀ {hd tl b}, inv (hd::tl) b →        -- vc₂: weaken invariant to precondition of loop body upon loop entry, done case
          obs⟦f hd b⟧ (∀ b', · = .done b'  → inv [] b'))
  (hyield : ∀ {hd tl b}, inv (hd::tl) b →       -- vc₃: weaken invariant to precondition of loop body upon loop entry, yield case
          obs⟦f hd b⟧ (∀ b', · = .yield b' → inv tl b')) :
  obs⟦forIn xs init f⟧ p := by
    induction xs generalizing init
    case nil => simp only [List.forIn_nil]; apply Obs.pure; apply hweaken; exact hpre
    case cons hd tl h =>
      simp only [List.forIn_cons]
      apply Obs.bind
      have : obs⟦f hd init⟧ (fun | .yield b' => inv tl b' | .done b' => inv [] b') :=
        Obs.split_step (hyield hpre) (hdone hpre)
      apply Obs.mono this
      intro r hres
      match r with
      | .done b => apply Obs.pure; apply hweaken; assumption
      | .yield b => simp; simp at hres; exact @h b hres

theorem Obs.forIn_range
  [Monad m] [LawfulMonad m]
  {xs : Std.Range} {init : β} {f : Nat → β → m (ForInStep β)}
  (inv : List Nat → β → Prop := fun _ => p)     -- user-supplied loop invariant
  (hpre : inv (List.range' xs.start xs.size xs.step) init)                          -- pre⟦for {inv} xs init f⟧(p)
  (hweaken : ∀ b, inv [] b → p b)               -- vc1: weaken invariant to postcondition after loop exit
  (hdone : ∀ {hd tl b}, inv (hd::tl) b →        -- vc₂: weaken invariant to precondition of loop body upon loop entry, done case
          obs⟦f hd b⟧ (∀ b', · = .done b'  → inv [] b'))
  (hyield : ∀ {hd tl b}, inv (hd::tl) b →       -- vc₃: weaken invariant to precondition of loop body upon loop entry, yield case
          obs⟦f hd b⟧ (∀ b', · = .yield b' → inv tl b')) :
  obs⟦forIn xs init f⟧ p := by
    rw [Std.Range.forIn_eq_forIn_range']
    exact Obs.forIn_list inv hpre hweaken hdone hyield

theorem Obs.forIn_loop
  [Monad m] [LawfulMonad m]
  {xs : Loop} {init : β} {f : Unit → β → m (ForInStep β)}
  (inv : Bool → β → Prop := fun _ => p)     -- user-supplied loop invariant
  (hpre : inv true init)                          -- pre⟦for {inv} xs init f⟧(p)
  (hweaken : ∀ b, inv false b → p b)               -- vc1: weaken invariant to postcondition after loop exit
  (hdone : ∀ {b}, inv true b →        -- vc₂: weaken invariant to precondition of loop body upon loop entry, done case
          obs⟦f () b⟧ (∀ b', · = .done b'  → inv false b'))
  (hyield : ∀ {b}, inv true b →       -- vc₃: weaken invariant to precondition of loop body upon loop entry, yield case
          obs⟦f () b⟧ (∀ b', · = .yield b' → inv true b')) :
  obs⟦forIn Loop.mk init f⟧ p := sorry

elab "vcgen" /-("invariant " ilbls:ident ": " inv:term)*-/ : tactic => withMainContext <| do
  let goal ← getMainGoal
  let ctx ← mkSimpContext Syntax.missing (eraseLocal := false)
  try
    let goal := match ← dsimpGoal goal ctx.ctx with
    | (some goal, _) => goal
    | _              => goal
    replaceMainGoal [goal]
  catch _ => pure ()
  let mut verification_conds := #[]
  while true do
    let goal :: goals ← getGoals | break
    if ← goal.isAssigned then setGoals goals; continue
    let (_xs, goal) ← goal.intros
    let ty ← instantiateMVars (← goal.getType)
    -- ty = @Obs m α [Functor m] prog post
    if ¬(ty.isAppOfArity `Obs 5) then
      logInfo m!"give up on {ty}"
      verification_conds := verification_conds.push goal
      setGoals goals
      continue
    let prog := ty.appFn!.appArg!
    let α := ty.appFn!.appFn!.appFn!.appArg!
    let m := ty.appFn!.appFn!.appFn!.appFn!.appArg!

    -- Convention: ⟦P⟧(x) for Obs P x
    if prog.isAppOfArity ``Pure.pure 4 then
      -- prog = @pure m [Pure m] α (x : α)
      -- ⟦P⟧(pure x)
      -- <=={Satisfies.pure}
      -- P x
      let [goal] ← goal.applyConst ``Obs.pure | throwError "argh"
      replaceMainGoal [goal]
      continue
    else if prog.isAppOfArity ``Bind.bind 6 then
      -- prog = @bind m [Bind m] α β e f
      -- ⟦P⟧(bind e f)
      -- <=={Satisfies.bind}
      -- P⟦fun r => ⟦P⟧(f r)⟧(e)
      let [goal] ← goal.applyConst ``Obs.bind | throwError "argh"
      replaceMainGoal [goal]
      continue
    else if prog.isAppOfArity ``ForIn.forIn 9 then
      -- prog = @forIn {m} {ρ} {α} [ForIn m ρ α] {β} [Monad m] xs init f
      -- ⟦P⟧(forIn xs init f)
      -- <=={Obs.forIn_*} (depending on ρ)
      -- ... a bunch of sub-goals, including the invariant
      let ρ := prog.appFn!.appFn!.appFn!.appFn!.appFn!.appFn!.appFn!.appArg!;
      if ρ.isConstOf ``Std.Range then
        let goals ← goal.applyConst ``Obs.forIn_range
        replaceMainGoal goals
        continue
      else if ρ.isConstOf ``List then
        let goals ← goal.applyConst ``Obs.forIn_range
        replaceMainGoal goals
        continue
      -- let name := match
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
    else if m.isConstOf ``Id then
      -- Id x is definitionally equal to x, and we can apply Obs.pure in that case
      -- prog = @pure m [Pure m] α (x : α)
      -- ⟦P⟧(pure x)
      -- <=={Satisfies.pure}
      -- P x
      let [goal] ← goal.applyConst ``Obs.pure | throwError "argh"
      replaceMainGoal [goal]
      continue
    else if α.isConstOf ``PUnit then
      -- If c : m PUnit, then the predicate is constant and can be pulled out
      -- ⟦P⟧(c)
      -- <=={Satisfies.split_unit}
      -- P ⟨⟩
      let [goal] ← goal.applyConst ``Obs.split_unit | throwError "argh"
      replaceMainGoal [goal]
      continue

    logInfo m!"give up on {repr prog}"
    verification_conds := verification_conds.push goal
    setGoals goals
    continue

  setGoals verification_conds.toList

theorem test_5 : Obs (m:=Id) (do let mut x := 0; for i in [1:5] do { x := x + i } return x) (fun r => r ≤ 25) := by
  vcgen
  case inv => exact (fun xs r => (∀ x, x ∈ xs → x ≤ 5) ∧ r + xs.length * 5 ≤ 25)
  set_option trace.grind.debug true in
  case hpre => simp_all; omega
  case hweaken => simp_all
  case hdone => simp_all
  case hyield h => injection h; simp_all; omega

theorem test_6 : Obs (m:=Id) (do let mut x := 0; let mut i := 0; while i < 4 do { x := x + i; i := i + 1 } return x) (fun r => r ≤ 1) := by
  dsimp
  vcgen
  case inv => exact (fun xs r => (∀ x, x ∈ xs → x ≤ 5) ∧ r + xs.length * 5 ≤ 25)
  case hpre => simp; omega
  case hweaken => simp
  case hdone => intros; apply Obs.pure; simp;
  case hyield => intros; apply Obs.pure; simp_all; intro _ h; injection h; omega

theorem test_1 : Obs (m:=Id) (do return 3) (fun r => r = 3) := by
  vcgen
  trivial

theorem test_2 : Obs (m:=Id) (do let mut id := 5; id := 3; return id) (fun r => r = 3) := by
  vcgen
  trivial

theorem test_3 [Monad m] [LawfulMonad m] (h : Obs e₁ (fun _ => Obs (m:=m) (do e₂; e₃) P)) : Obs (m:=m) (do e₁; e₂; e₃) P := by
  vcgen
  trivial

theorem test_4 : Obs (m:=Id) (do let mut x := 5; if x > 1 then { x := 1 } else { x := x }; pure x) (fun r => r ≤ 1) := by
  vcgen <;> simp; omega

def fib_impl (n : Nat) := Id.run do
  if n = 0 then return 0
  let mut a := 0
  let mut b := 0
  b := b + 1
  for _ in [1:n] do
    let a' := a
    a := b
    b := a' + b
  return b

def fib_spec : Nat → Nat
| 0 => 0
| 1 => 1
| n+2 => fib_spec n + fib_spec (n+1)

theorem fib_correct {n} : fib_impl n = fib_spec n := Obs_Id_eq (P := fun r => r = fib_spec n) <| by
  vcgen
  case isTrue => simp_all[fib_spec]
  case inv => exact (fun | xs, ⟨a, b⟩ => a = fib_spec (n - xs.length - 1) ∧ b = fib_spec (n - xs.length))
  case hpre col _ h =>
    simp_all[List.range']
    have : 1 ≤ n := Nat.succ_le_of_lt (Nat.zero_lt_of_ne_zero h)
    rw[Nat.div_one, Nat.sub_one_add_one h, Nat.sub_sub, Nat.sub_add_cancel this, Nat.sub_self, Nat.sub_sub_self this]
    simp_all[fib_spec]
    exact ⟨rfl, rfl⟩
  case hweaken => apply Obs.pure; simp_all
  case hdone.hx.h.h => simp_all
  case hyield.hx.h.h b' h => injection h; subst b'; subst_vars; simp_all; rw[fib_spec] at ⊢;
  -- The default simp set eliminates the binds generated by `do` notation,
  -- and converts the `for` loop into a `List.foldl` over `List.range'`.
  simp [fib_impl, Id.run]
  match n with
  | 0 => simp [fib_spec]
  | n+1 =>
    -- Note here that we have to use `⟨x, y⟩ : MProd _ _`, because these are not `Prod` products.
    suffices ((List.range' 1 n).foldl (fun b a ↦ ⟨b.snd, b.fst + b.snd⟩) (⟨0, 1⟩ : MProd _ _)) =
        ⟨fib_spec n, fib_spec (n + 1)⟩ by simp_all
    induction n with
    | zero => rfl
    | succ n ih => simp [fib_spec, List.range'_1_concat, ih]
/-
https://lean-fro.zulipchat.com/#narrow/channel/398861-general/topic/baby.20steps.20towards.20monadic.20verification

-/

class MonadObserve (m : Type u₁ → Type u₂) [Monad com] [LawfulMonad com] [Monad spec] [LawfulMonad spec] where
  observe : com α → spec α
  pure_pure : ∀ {a : α} {p : α → prop}, p a → observe (pure a) p

class MonadPost (m : Type u₁ → Type u₂) (prop : Type) [Monad m] [LawfulMonad m] where
  Post : m α → Prop
  pure {a : α} {p : α → prop} (hp : p a) : Post (pure a)
  bind {α β} (x : m α) (f : α → m β) {p : β → prop} : Post x (fun a => Post (f a) p) → Post (x >>= f) p
  forIn_list {α β} {xs : List α} {init : β} {f : α → β → m (ForInStep β)} {p : α → prop}
    (inv : List α → β → Prop)                     -- user-supplied loop invariant
    (hpre : inv xs init)                          -- pre⟦for {inv} xs init f⟧(p)
    (hweaken : ∀ b, inv [] b → p b)               -- vc₁: weaken invariant to postcondition after loop exit
    (hdone : ∀ {hd tl b}, inv (hd::tl) b →        -- vc₂: weaken invariant to precondition of loop body upon loop entry, done case
            Post (f hd b) (∀ b', · = .done b'  → inv [] b'))
    (hyield : ∀ {hd tl b}, inv (hd::tl) b →       -- vc₃: weaken invariant to precondition of loop body upon loop entry, yield case
          Post (f hd b) (∀ b', · = .yield b' → inv tl b')) :
      Post (forIn xs init f) p


def StateT.observe {m : Type u → Type v} {α} [Monad m] (x : StateT σ m α) : StateT σ PredTransM α := fun s₁ p =>
  Obs (do set s₁; let a ← x; let s₂ ← get; pure (a, s₂)) p

theorem blah {a : α} {s : σ} : (fun p => p (a, s)) → (do s ← Obs get; Obs (Pure.pure (a, s))) := by
  intro h
  simp only [observe]
  vcgen
  assumption

theorem StateT.observe.pure {m : Type u → Type v} {p : α × σ → Prop} [Monad m] [LawfulMonad m]
  (hp : p (a, s)) : StateT.observe (m:=m) (pure a) s p := by
  simp only [observe, pure_bind, LawfulMonadState.set_get]
  vcgen
  assumption

theorem StateT.observe.get_pre {m : Type u → Type v} [Monad m] [LawfulMonad m] {p : σ × σ → Prop} (hp : p ⟨s, s⟩) :
  StateT.observe (m:=m) get s p := by
  simp only [observe, pure_bind, LawfulMonadState.set_get]
  vcgen
  assumption

theorem StateT.observe.get {m : Type u → Type v} [Monad m] [LawfulMonad m] :
  StateT.observe (m:=m) get s (· = ⟨s, s⟩) := StateT.observe.get_pre (by rfl)

theorem StateT.observe.set_pre {m : Type u → Type v} [Monad m] [LawfulMonad m] {p : PUnit × σ → Prop} (hp : p ⟨⟨⟩, s₂⟩) :
  StateT.observe (m:=m) (set s₂) s₁ p := by
  simp only [observe, pure_bind, Monad.bind_unit]
  simp only [← LawfulMonad.bind_assoc, LawfulMonadState.set_set]
  simp only [LawfulMonadState.set_get_pure]
  simp [-LawfulMonad.bind_pure_comp]
  vcgen
  assumption

theorem StateT.observe.set {m : Type u → Type v} [Monad m] [LawfulMonad m] {s₂ : σ} :
  StateT.observe (m:=m) (set s₂) s₁ (· = ⟨⟨⟩, s₂⟩) := StateT.observe.set_pre (by rfl)



/-
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

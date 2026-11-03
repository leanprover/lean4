import Lean.Meta.Sym

open Lean Meta Sym

/-! ## Level commutativity: `max u v` vs `max v u` with concrete params -/

/--
info: rule.apply succeeds: max u v matches max v u
-/
#guard_msgs in
#eval show MetaM Unit from do
  let u := Level.param `u
  let v := Level.param `v
  let maxUV := Level.max u v
  let maxVU := Level.max v u
  let proof := mkApp2 (mkConst ``Eq.refl [maxUV.succ]) (mkSort maxUV) (mkSort maxUV)
  let rule ← mkBackwardRuleFromExpr proof (levelParams := [`u, `v])
  let goalType := mkApp3 (mkConst ``Eq [maxVU.succ]) (mkSort maxVU) (mkSort maxVU) (mkSort maxVU)
  let r ← SymM.run do
    let mvar ← mkFreshExprMVar goalType
    let mvarId ← preprocessMVar mvar.mvarId!
    rule.apply mvarId
  match r with
  | .goals _ => logInfo "rule.apply succeeds: max u v matches max v u"
  | .failed  => logInfo "rule.apply FAILED: max u v did not match max v u"

/-! ## `tryApproxMaxMax`: pattern `max _uvar 1` matching target `max 1 u` -/

axiom lvlAxiom : ∀ (α : Sort (max u 1)), α → α

/--
info: pattern match succeeded
-/
#guard_msgs in
#eval show MetaM Unit from do
  let pat ← mkPatternFromDecl ``lvlAxiom
  -- Target has `max 1 u` (swapped from pattern's `max u 1`)
  let u := Level.param `u
  let lvl := Level.max (.succ .zero) u  -- max 1 u
  let targetType := Expr.forallE `α (.sort lvl) (Expr.forallE `a (.bvar 0) (.bvar 1) .default) .implicit
  let r ← SymM.run do
    pat.match? targetType
  match r with
  | some _ => logInfo "pattern match succeeded"
  | none   => logInfo "pattern match FAILED"

/-! ## Delay `max` constraints whose uvars are determined elsewhere (#16070) -/

theorem id_prod {α : Type u} {β : Type v} (p : α × β) : @id (α × β) p = p := rfl

example {α : Type u} {β : Type (max v w)} (p : α × β) : @id (α × β) p = p := by
  sym => simp [id_prod]

example {α : Type u} {β : Type v} (p : β × α) : @id (β × α) p = p := by
  sym => simp [id_prod]

example {α : Type (max u v)} {β : Type u} (p : α × β) : @id (α × β) p = p := by
  sym => simp [id_prod]

example {α : Type u} {β : Type (max v w)} (p : α × β) (q : α × β) (h : p = q) : @id (α × β) p = q := by
  sym =>
    dsimp [id_prod]
    exact h

example {α : Type u} {β : Type (max v w)} (p : α × β) : @id (α × β) p = p := by
  sym => apply id_prod

/-! The universe variables occur only inside a `max`, so nothing else determines them. -/

set_option linter.checkUnivs false in
theorem id_max_succ (α : Type (max u v)) (a : α) : @id α a = a := rfl

example (α : Type (max u v w)) (a : α) : @id α a = a := by
  sym => simp [id_max_succ]

set_option linter.checkUnivs false in
theorem id_max_sort (α : Sort (max u v)) (a : α) : @id α a = a := rfl

example (α : Sort (max u v w)) (a : α) : @id α a = a := by
  sym => simp [id_max_sort]

/-! Direct `match?`/`unify?` calls on `@id.{l} (Prod.{u₁, u₂} α β) p`. -/

namespace DirectMatch

def matchIdProd (l u₁ u₂ : Level) (unify := false) : MetaM Unit := do
  let (pat, _) ← mkEqPatternFromDecl ``id_prod
  withLocalDeclD `α (mkSort u₁.succ) fun α =>
  withLocalDeclD `β (mkSort u₂.succ) fun β => do
  let prod := mkApp2 (mkConst ``Prod [u₁, u₂]) α β
  withLocalDeclD `p prod fun p => do
  let e := mkApp2 (mkConst ``id [l]) prod p
  let r ← SymM.run do
    let e ← shareCommon e
    if unify then pat.unify? e else pat.match? e
  match r with
  | some r => logInfo m!"{r.us}"
  | none   => logInfo "failed"

def u := Level.param `u
def v := Level.param `v
def w := Level.param `w

/-- info: [u, max v w] -/
#guard_msgs in
#eval matchIdProd (mkLevelMax u.succ (mkLevelMax v w).succ) u (mkLevelMax v w)

/-- info: [max u v, w] -/
#guard_msgs in
#eval matchIdProd (mkLevelMax (mkLevelMax u v).succ w.succ) (mkLevelMax u v) w

/-- info: [v, u] -/
#guard_msgs in
#eval matchIdProd (mkLevelMax u.succ v.succ) v u

/-! The delayed constraint is checked: `id`'s level does not match the `Prod` levels. -/

/-- info: failed -/
#guard_msgs in
#eval matchIdProd (mkLevelMax u.succ v.succ) u (mkLevelMax v w)

/-! Level metavariables in the target (`unify?`): the delayed constraint relates `?m` and `?n`. -/

/-- info: true -/
#guard_msgs in
#eval show MetaM Unit from do
  let (pat, _) ← mkEqPatternFromDecl ``id_prod
  let m ← mkFreshLevelMVar
  let n ← mkFreshLevelMVar
  withLocalDeclD `α (mkSort u.succ) fun α =>
  withLocalDeclD `β (mkSort n.succ) fun β => do
  let prod := mkApp2 (mkConst ``Prod [u, n]) α β
  withLocalDeclD `p prod fun p => do
  let e := mkApp2 (mkConst ``id [mkLevelMax u.succ m.succ]) prod p
  let some r ← SymM.run do pat.unify? (← shareCommon e) | logInfo "failed"
  let us ← r.us.mapM instantiateLevelMVars
  logInfo m!"{us == [u, ← instantiateLevelMVars m]}"

end DirectMatch

/-! More `sym` rewrites -/

theorem id_prod3 {α : Type u} {β : Type v} {γ : Type w} (p : α × β × γ) : @id (α × β × γ) p = p := rfl

example {α : Type (max u v)} {β : Type w} {γ : Type (max u x)} (p : α × β × γ) : @id (α × β × γ) p = p := by
  sym => simp [id_prod3]

example {α : Type (max u x)} {β : Type (max v w)} (p : α × β) : @id (α × β) p = p := by
  sym => simp [id_prod]

example {α : Type (max u v)} {β : Type (max v u)} (p : α × β) : @id (α × β) p = p := by
  sym => simp [id_prod]

example {α : Type u} (p : α × Nat) : @id (α × Nat) p = p := by
  sym => simp [id_prod]

example {α β : Type u} (p : α × β) : @id (α × β) p = p := by
  sym => simp [id_prod]

/-! `imax` -/

theorem id_pi {α : Sort u} {β : α → Sort v} (f : (a : α) → β a) : @id ((a : α) → β a) f = f := rfl

example {α : Sort u} {β : α → Sort (max v w)} (f : (a : α) → β a) : @id ((a : α) → β a) f = f := by
  sym => simp [id_pi]

/-! `Sort` patterns -/

theorem id_type_prod (α : Type u) (β : Type v) : @id (Type (max u v)) (α × β) = (α × β) := rfl

example (α : Type u) (β : Type (max v w)) : @id (Type (max u v w)) (α × β) = (α × β) := by
  sym => simp [id_type_prod]

/-! `Prop` components -/

theorem id_pprod {α : Sort u} {β : Sort v} (p : PProd α β) : @id (PProd α β) p = p := rfl

example {α : Prop} {β : Sort (max v w)} (p : PProd α β) : @id (PProd α β) p = p := by
  sym => simp [id_pprod]

/-! Instance not in the LHS, synthesized after the delayed constraint is solved. -/

theorem id_prod_inst {α : Type u} {β : Type v} [Nonempty α] (p : α × β) : @id (α × β) p = p := rfl

example {α : Type u} {β : Type (max v w)} [Nonempty α] (p : α × β) : @id (α × β) p = p := by
  sym => simp [id_prod_inst]

/-! The universe variables are determined only by the types of the pattern variables. -/

theorem id_arrow {α : Type u} {β : Type v} (f : α → β) (a : α) : @id (α → β) f a = f a := rfl

example {α : Type u} {β : Type (max v w)} (f : α → β) (a : α) : @id (α → β) f a = f a := by
  sym => simp [id_arrow]

example {β : Type (max v w)} (f : Nat → List β) (a : Nat) : @id (Nat → List β) f a = f a := by
  sym => simp [id_arrow]

theorem id_pi_type {α : Type u} {β : α → Type v} (f : (a : α) → β a) : @id ((a : α) → β a) f = f := rfl

example {α : Type u} {β : α → Type (max v w)} (f : (a : α) → β a) : @id ((a : α) → β a) f = f := by
  sym => simp [id_pi_type]

theorem pi_id_apply {I : Type u} {f : I → Type v} (x : (i : I) → f i) (i : I) : @id ((i : I) → f i) x i = x i := rfl

example {I : Type u} {f : I → Type (max v w)} (x : (i : I) → f i) (i : I) : @id ((i : I) → f i) x i = x i := by
  sym => simp [pi_id_apply]

theorem id_arrow3 {α : Type u} {β : Type v} {γ : Type w} (f : α → β → γ) : @id (α → β → γ) f = f := rfl

example {α : Type (max u x)} {β : Type v} {γ : Type (max w x)} (f : α → β → γ) : @id (α → β → γ) f = f := by
  sym => simp [id_arrow3]

theorem id_lam {α : Type u} {β : Type v} (g : α → β) : @id (α → β) (fun x => g x) = g := rfl

example {α : Type u} {β : Type (max v w)} (g : α → β) : @id (α → β) (fun x => g x) = g := by
  sym => simp [id_lam]

theorem fun_eq_iff {α : Type u} {β : Type v} (f g : α → β) : (f = g) = ∀ a, f a = g a :=
  propext ⟨fun h _ => h ▸ rfl, funext⟩

example {α : Type u} {β : Type (max v w)} (f g : α → β) (h : ∀ a, f a = g a) : f = g := by
  sym =>
    simp [fun_eq_iff]
    exact h

/-! Universes derived from the types must still be consistent with the pattern. -/

theorem id_arrow_same {α β : Type u} (f : α → β) : @id (α → β) f = f := rfl

/-- error: `Sym.simp` made no progress -/
#guard_msgs in
example {α : Type u} {β : Type (max u v)} (f : α → β) : @id (α → β) f = f := by
  sym => simp [id_arrow_same]

example {α : Type u} {β : Type (max v w)} (f : α → β) (a : α) : @id (α → β) f a = f a := by
  sym => apply id_arrow

theorem eq_arrow {α : Type u} {β : Type v} {f g : α → β} (h : ∀ a, f a = g a) : f = g := funext h

example {α : Type u} {β : Type (max v w)} (f g : α → β) (h : ∀ a, f a = g a) : f = g := by
  sym =>
    apply eq_arrow
    exact h

/-! Some universe variables are determined by `Prod`, the others only by the types. -/

theorem id_prod_arrow {α : Type u} {β : Type v} {γ : Type w} (p : α × (β → γ)) : @id (α × (β → γ)) p = p := rfl

example {α : Type (max u x)} {β : Type v} {γ : Type (max w x)} (p : α × (β → γ)) : @id (α × (β → γ)) p = p := by
  sym => simp [id_prod_arrow]

theorem id_prod_arrow_same {α : Type u} {β γ : Type v} (p : α × (β → γ)) : @id (α × (β → γ)) p = p := rfl

/-- error: `Sym.simp` made no progress -/
#guard_msgs in
example {α : Type u} {β : Type v} {γ : Type (max v w)} (p : α × (β → γ)) : @id (α × (β → γ)) p = p := by
  sym => simp [id_prod_arrow_same]

/-! A shared argument between both `max` levels. -/

set_option linter.checkUnivs false in
theorem id_max_one (α : Sort (max u 1)) (a : α) : @id α a = a := rfl

example (α : Sort (max 1 v)) (a : α) : @id α a = a := by
  sym => simp [id_max_one]

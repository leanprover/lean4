%reset_grind_attrs

attribute [grind cases] Or
attribute [grind =] List.length_nil List.length_cons Option.getD

set_option profiler true

abbrev Var := String

inductive Val where
  | int  (i : Int)
  | bool (b : Bool)
  deriving DecidableEq, Repr

instance : Coe Bool Val where
  coe b := .bool b

instance : OfNat Val n where
  ofNat := .int n

inductive BinOp where
  | eq | and | lt | add | sub
  deriving Repr

inductive UnaryOp where
  | not
  deriving Repr

inductive Expr where
  | val (v : Val)
  | var (x : Var)
  | bin (lhs : Expr) (op : BinOp) (rhs : Expr)
  | una (op : UnaryOp) (arg : Expr)
  deriving Repr

@[simp, grind =] def BinOp.eval : BinOp → Val → Val → Option Val
  | .eq,  v₁,        v₂      => some (.bool (v₁ = v₂))
  | .and, .bool b₁, .bool b₂ => some (.bool (b₁ && b₂))
  | .lt,  .int i₁,  .int i₂  => some (.bool (i₁ < i₂))
  | .add, .int i₁,  .int i₂  => some (.int (i₁ + i₂))
  | .sub, .int i₁,  .int i₂  => some (.int (i₁ - i₂))
  | _,    _,        _        => none

@[simp, grind =] def UnaryOp.eval : UnaryOp → Val → Option Val
  | .not, .bool b => some (.bool !b)
  | _,    _       => none

inductive Stmt where
  | skip
  | assign (x : Var) (e : Expr)
  | seq    (s₁ s₂ : Stmt)
  | ite    (c : Expr) (e t : Stmt)
  | while  (c : Expr) (b : Stmt)

infix:150 " ::= " => Stmt.assign
infixr:130 ";; "   => Stmt.seq

abbrev State := List (Var × Val)

@[simp] def State.update (σ : State) (x : Var) (v : Val) : State :=
  match σ with
  | [] => [(x, v)]
  | (y, w)::σ => if x = y then (x, v)::σ else (y, w) :: update σ x v

@[simp] def State.find? (σ : State) (x : Var) : Option Val :=
  match σ with
  | [] => none
  | (y, v) :: σ => if x = y then some v else find? σ x

def State.get (σ : State) (x : Var) : Val :=
  σ.find? x |>.getD (.int 0)

@[simp] def State.erase (σ : State) (x : Var) : State :=
  match σ with
  | [] => []
  | (y, v) :: σ => if x = y then erase σ x else (y, v) :: erase σ x

section
attribute [local grind] State.update State.find? State.get State.erase

@[simp, grind =] theorem State.find?_update_self (σ : State) (x : Var) (v : Val) : (σ.update x v).find? x = some v := by
  induction σ, x, v using State.update.induct <;> grind

@[simp, grind =] theorem State.find?_update (σ : State) (v : Val) (h : x ≠ z) : (σ.update x v).find? z = σ.find? z := by
  induction σ, x, v using State.update.induct <;> grind

@[grind] theorem State.get_of_find? {σ : State} (h : σ.find? x = some v) : σ.get x = v := by
  grind

@[simp, grind =] theorem State.find?_erase_self (σ : State) (x : Var) : (σ.erase x).find? x = none := by
  induction σ, x using State.erase.induct <;> grind

@[simp, grind =] theorem State.find?_erase (σ : State) (h : x ≠ z) : (σ.erase x).find? z = σ.find? z := by
  induction σ, x using State.erase.induct <;> grind
end

syntax ident " ↦ " term : term

macro_rules
  | `($id:ident ↦ $v:term) => `(($(Lean.quote id.getId.toString), $v:term))

example : State.get [x ↦ .int 10, y ↦ .int 20] "x" = .int 10 := rfl

example : State.get [x ↦ 10, y ↦ 20] "x" = 10     := rfl
example : State.get [x ↦ 10, y ↦ true] "y" = true := rfl

@[simp, grind =] def Expr.eval (σ : State) : Expr → Option Val
  | val v   => some v
  | var x   => σ.get x
  | bin lhs op rhs => match lhs.eval σ, rhs.eval σ with
    | some v₁, some v₂ => op.eval v₁ v₂  -- BinOp.eval : BinOp → Val → Val → Option Val
    | _,       _       => none
  | una op arg => match arg.eval σ with
    | some v => op.eval v
    | _      => none

@[simp, grind =] def evalTrue  (c : Expr) (σ : State) : Prop := c.eval σ = some (Val.bool true)
@[simp, grind =] def evalFalse (c : Expr) (σ : State) : Prop := c.eval σ = some (Val.bool false)

section
set_option hygiene false -- HACK: allow forward reference in notation
local notation:60 "(" σ ", " s ")"  " ⇓ " σ':60 => Bigstep σ s σ'

inductive Bigstep : State → Stmt → State → Prop where
  | skip       : (σ, .skip) ⇓ σ
  | assign     : e.eval σ = some v → (σ,  x ::= e) ⇓ σ.update x v
  | seq        : (σ₁, s₁) ⇓ σ₂ → (σ₂, s₂) ⇓ σ₃ → (σ₁, s₁ ;; s₂) ⇓ σ₃
  | ifTrue     : evalTrue c σ₁ → (σ₁, t) ⇓ σ₂ → (σ₁, .ite c t e) ⇓ σ₂
  | ifFalse    : evalFalse c σ₁ → (σ₁, e) ⇓ σ₂ → (σ₁, .ite c t e) ⇓ σ₂
  | whileTrue  : evalTrue c σ₁ → (σ₁, b) ⇓ σ₂ → (σ₂, .while c b) ⇓ σ₃ → (σ₁, .while c b) ⇓ σ₃
  | whileFalse : evalFalse c σ → (σ, .while c b) ⇓ σ

end

notation:60 "(" σ ", " s ")"  " ⇓ " σ':60 => Bigstep σ s σ'

/- This proof can be automated using forward reasoning. -/
theorem Bigstem.det (h₁ : (σ, s) ⇓ σ₁) (h₂ : (σ, s) ⇓ σ₂) : σ₁ = σ₂ := by
  induction h₁ generalizing σ₂ <;> grind [Bigstep]

abbrev EvalM := ExceptT String (StateM State)

def evalExpr (e : Expr) : EvalM Val := do
  match e.eval (← get) with
  | some v => return v
  | none => throw "failed to evaluate"

@[simp, grind =] def Stmt.eval (stmt : Stmt) (fuel : Nat := 100) : EvalM Unit := do
  match fuel with
  | 0 => throw "out of fuel"
  | fuel+1 =>
    match stmt with
    | skip        => return ()
    | assign x e  => let v ← evalExpr e; modify fun s => s.update x v
    | seq s₁ s₂   => s₁.eval fuel; s₂.eval fuel
    | ite c e t   =>
      match (← evalExpr c) with
      | .bool true  => e.eval fuel
      | .bool false => t.eval fuel
      | _ => throw "Boolean expected"
    | .while c b =>
      match (← evalExpr c) with
      | .bool true  => b.eval fuel; stmt.eval fuel
      | .bool false => return ()
      | _ => throw "Boolean expected"

@[simp, grind =] def BinOp.simplify : BinOp → Expr → Expr → Expr
  | .eq,  .val v₁,  .val  v₂ => .val (.bool (v₁ = v₂))
  | .and, .val (.bool a), .val (.bool b) => .val (.bool (a && b))
  | .lt,  .val (.int a),  .val (.int b)  => .val (.bool (a < b))
  | .add, .val (.int a), .val (.int b) => .val (.int (a + b))
  | .sub, .val (.int a), .val (.int b) => .val (.int (a - b))
  | op, a, b => .bin a op b

@[simp, grind =] def UnaryOp.simplify : UnaryOp → Expr → Expr
  | .not, .val (.bool b) => .val (.bool !b)
  | op, a => .una op a

@[simp, grind =] def Expr.simplify : Expr → Expr
  | bin lhs op rhs => op.simplify lhs.simplify rhs.simplify
  | una op arg => op.simplify arg.simplify
  | e => e

@[simp, grind =] theorem Expr.eval_simplify (e : Expr) : e.simplify.eval σ = e.eval σ := by
  induction e <;> try grind [BinOp.simplify.eq_def, UnaryOp.simplify.eq_def]
  next op arg ih_arg =>
    simp only [simplify, UnaryOp.simplify, eval, ← ih_arg, UnaryOp.eval]
    split
    · grind (splits := 0) [Expr.eval] -- TODO: investigate: why do we need Expr.eval here
    · simp only [eval, UnaryOp.eval] -- TODO: `grind` failes here

@[simp, grind =] def Stmt.simplify : Stmt → Stmt
  | skip => skip
  | assign x e => assign x e.simplify
  | seq s₁ s₂ => seq s₁.simplify s₂.simplify
  | ite c e t =>
    match c.simplify with
    | .val (.bool true) => e.simplify
    | .val (.bool false) => t.simplify
    | c' => ite c' e.simplify t.simplify
  | .while c b =>
    match c.simplify with
    | .val (.bool false) => skip
    | c' => .while c' b.simplify

theorem Stmt.simplify_correct (h : (σ, s) ⇓ σ') : (σ, s.simplify) ⇓ σ' := by
  -- TODO: we need a mechanism for saying we just want the intro rules
  induction h <;> try grind [Bigstep]
  next => grind [=_ Expr.eval_simplify, Bigstep.ifTrue]
  next => grind [=_ Expr.eval_simplify, Bigstep.ifFalse]
  next => grind [=_ Expr.eval_simplify, Bigstep.whileTrue]

@[simp, grind =] def Expr.constProp (e : Expr) (σ : State) : Expr :=
  match e with
  | val v => val v
  | var x => match σ.find? x with
    | some v => val v
    | none   => var x
  | bin lhs op rhs => bin (lhs.constProp σ) op (rhs.constProp σ)
  | una op arg => una op (arg.constProp σ)

@[simp, grind =] theorem Expr.constProp_nil (e : Expr) : e.constProp [] = e := by
  induction e <;> grind [State.find?] -- TODO add missing theorem(s) to avoid unfolding `find?`

@[grind] theorem State.length_erase_le (σ : State) (x : Var) : (σ.erase x).length ≤ σ.length := by
  induction σ, x using erase.induct <;> grind [State.erase] -- TODO add missing theorem(s)

def State.length_erase_lt (σ : State) (x : Var) : (σ.erase x).length < σ.length.succ :=
  -- TODO: offset issues?
  Nat.lt_of_le_of_lt (length_erase_le ..) (by grind)

@[simp, grind =] def State.join (σ₁ σ₂ : State) : State :=
  match σ₁ with
  | [] => []
  | (x, v) :: σ₁ =>
    let σ₁' := erase σ₁ x -- Must remove duplicates. Alternative design: carry invariant that input state at constProp has no duplicates
    have : (erase σ₁ x).length < σ₁.length.succ := length_erase_lt ..
    match σ₂.find? x with
    | some w => if v = w then (x, v) :: join σ₁' σ₂ else join σ₁' σ₂
    | none => join σ₁' σ₂
termination_by σ₁.length

local notation "⊥" => []

@[simp, grind =] def Stmt.constProp (s : Stmt) (σ : State) : Stmt × State :=
  match s with
  | skip => (skip, σ)
  | assign x e => match (e.constProp σ).simplify with
    | (.val v) => (assign x (.val v), σ.update x v)
    | e'       => (assign x e', σ.erase x)
  | seq s₁ s₂ => match s₁.constProp σ with
    | (s₁', σ₁) => match s₂.constProp σ₁ with
      | (s₂', σ₂) => (seq s₁' s₂', σ₂)
  | ite c s₁ s₂ =>
    match s₁.constProp σ, s₂.constProp σ with
    | (s₁', σ₁), (s₂', σ₂) => (ite (c.constProp σ) s₁' s₂', σ₁.join σ₂)
  | .while c b => (.while (c.constProp ⊥) (b.constProp ⊥).1, ⊥)

def State.le (σ₁ σ₂ : State) : Prop :=
  ∀ ⦃x : Var⦄ ⦃v : Val⦄, σ₁.find? x = some v → σ₂.find? x = some v

infix:50 " ≼ " => State.le

@[grind] theorem State.le_refl (σ : State) : σ ≼ σ :=
  fun _ _ h => h

section
attribute [local grind] State.le State.erase State.find? State.update

theorem State.le_trans : σ₁ ≼ σ₂ → σ₂ ≼ σ₃ → σ₁ ≼ σ₃ := by
  grind

theorem State.bot_le (σ : State) : ⊥ ≼ σ := by
  grind

theorem State.erase_le_cons (h : σ' ≼ σ) : σ'.erase x ≼ ((x, v) :: σ) := by
  grind

theorem State.cons_le_cons (h : σ' ≼ σ) : (x, v) :: σ' ≼ (x, v) :: σ := by
  grind

theorem State.cons_le_of_eq (h₁ : σ' ≼ σ) (h₂ : σ.find? x = some v) : (x, v) :: σ' ≼ σ := by
  grind

@[grind] theorem State.erase_le (σ : State) : σ.erase x ≼ σ := by
  induction σ, x using State.erase.induct <;> grind

@[grind] theorem State.join_le_left (σ₁ σ₂ : State) : σ₁.join σ₂ ≼ σ₁ := by
  induction σ₁, σ₂ using State.join.induct <;> grind

@[grind] theorem State.join_le_left_of (h : σ₁ ≼ σ₂) (σ₃ : State) : σ₁.join σ₃ ≼ σ₂ := by
  grind

@[grind] theorem State.join_le_right (σ₁ σ₂ : State) : σ₁.join σ₂ ≼ σ₂ := by
  induction σ₁, σ₂ using State.join.induct <;> grind

@[grind] theorem State.join_le_right_of (h : σ₁ ≼ σ₂) (σ₃ : State) : σ₃.join σ₁ ≼ σ₂ := by
  grind

theorem State.eq_bot (h : σ ≼ ⊥) : σ = ⊥ := by
  match σ with
  | [] => grind
  | (y, v) :: σ =>
    -- TODO: can we avoid this hint?
    have : State.find? ((y, v) :: σ) y = some v := by grind
    grind

theorem State.erase_le_of_le_cons (h : σ' ≼ (x, v) :: σ) : σ'.erase x ≼ σ := by
  grind

@[grind] theorem State.erase_le_update (h : σ' ≼ σ) : σ'.erase x ≼ σ.update x v := by
  intro y w hf'
  -- TODO: can we avoid this hint?
  by_cases hxy : x = y <;> grind

@[grind] theorem State.update_le_update (h : σ' ≼ σ) : σ'.update x v ≼ σ.update x v := by
  intro y w hf
  induction σ generalizing σ' hf with
  | nil  => grind
  | cons zw' σ ih =>
    have (z, w') := zw'; simp
    have : σ'.erase z ≼ σ := erase_le_of_le_cons h
    have ih := ih this
    revert ih hf
    split <;> simp [*] <;> by_cases hyz : y = z <;> simp (config := { contextual := true }) [*]
    next => grind
    next => grind
    sorry

-- TODO: we are missing theorems here, and cannot seal State functions
@[grind] theorem Expr.eval_constProp_of_sub (e : Expr) (h : σ' ≼ σ) : (e.constProp σ').eval σ = e.eval σ := by
  induction e <;> grind

theorem Expr.eval_constProp_of_eq_of_sub {e : Expr} (h₁ : e.eval σ = v) (h₂ : σ' ≼ σ) : (e.constProp σ').eval σ = v := by
  grind

theorem Stmt.constProp_sub (h₁ : (σ₁, s) ⇓ σ₂) (h₂ : σ₁' ≼ σ₁) : (s.constProp σ₁').2 ≼ σ₂ := by
  induction h₁ generalizing σ₁' with try grind
  | assign heq =>
    simp
    split <;> simp
    next h =>
      have heq' := Expr.eval_constProp_of_eq_of_sub heq h₂
      rw [← Expr.eval_simplify, h] at heq'
      grind
    next => grind
  | ifTrue heq h ih =>
    have ih := ih h₂
    apply State.join_le_left_of ih
  | ifFalse heq h ih =>
    have ih := ih h₂
    apply State.join_le_right_of ih
  | seq h₃ h₄ ih₃ ih₄ =>
    exact ih₄ (ih₃ h₂)

end

theorem Stmt.constProp_correct (h₁ : (σ₁, s) ⇓ σ₂) (h₂ : σ₁' ≼ σ₁) : (σ₁, (s.constProp σ₁').1) ⇓ σ₂ := by
  induction h₁ generalizing σ₁' with simp_all
  | skip => grind [Bigstep]
  | assign heq =>
    split <;> simp
    next h =>
      have heq' := Expr.eval_constProp_of_eq_of_sub heq h₂
      rw [← Expr.eval_simplify, h] at heq'
      simp at heq'
      apply Bigstep.assign; simp only [Expr.eval, heq']
    next =>
      have heq' := Expr.eval_constProp_of_eq_of_sub heq h₂
      rw [← Expr.eval_simplify] at heq'
      apply Bigstep.assign heq'
  | seq h₁ h₂ ih₁ ih₂ =>
    apply Bigstep.seq (ih₁ h₂) (ih₂ (constProp_sub h₁ h₂))
  | whileTrue heq h₁ h₂ ih₁ ih₂ =>
    have ih₁ := ih₁ (State.bot_le _)
    have ih₂ := ih₂ (State.bot_le _)
    exact Bigstep.whileTrue heq ih₁ ih₂
  | whileFalse heq =>
    grind [Bigstep]
  | ifTrue heq h ih =>
    -- TODO: `grind` did not manage to find pattern or `Expr.eval_constProp_of_eq_of_sub`
    have := Expr.eval_constProp_of_eq_of_sub heq h₂
    grind [Bigstep]
  | ifFalse heq h ih =>
    have := Expr.eval_constProp_of_eq_of_sub heq h₂
    grind [Bigstep]

def Stmt.constPropagation (s : Stmt) : Stmt :=
  (s.constProp ⊥).1

theorem Stmt.constPropagation_correct (h : (σ, s) ⇓ σ') : (σ, s.constPropagation) ⇓ σ' := by
  -- TODO: grind [constProp_correct, State.bot_le]
  exact constProp_correct h (State.bot_le _)

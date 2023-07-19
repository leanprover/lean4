abbrev Var := String

inductive Val where
  | int  (i : Int)
  | bool (b : Bool)
  deriving DecidableEq, Repr

instance : Coe Bool Val where
  coe b := .bool b

instance : Coe Int Val where
  coe i := .int i

instance : OfNat Val n where
  ofNat := .int n

#check (true : Val)

#check (0 : Val)

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

instance : Coe Val Expr where
  coe v := .val v

instance : Coe Var Expr where
  coe x := .var x

instance : OfNat Expr n where
  ofNat := .val n

@[simp] def BinOp.eval : BinOp → Val → Val → Option Val
  | .eq,  v₁,        v₂      => some (.bool (v₁ = v₂))
  | .and, .bool b₁, .bool b₂ => some (.bool (b₁ && b₂))
  | .lt,  .int i₁,  .int i₂  => some (.bool (i₁ < i₂))
  | .add, .int i₁,  .int i₂  => some (.int (i₁ + i₂))
  | .sub, .int i₁,  .int i₂  => some (.int (i₁ - i₂))
  | _,    _,        _        => none

@[simp] def UnaryOp.eval : UnaryOp → Val → Option Val
  | .not, .bool b => some (.bool !b)
  | _,    _       => none

inductive Stmt where
  | skip
  | assign (x : Var) (e : Expr)
  | seq    (s₁ s₂ : Stmt)
  | ite    (c : Expr) (e t : Stmt)
  | while  (c : Expr) (b : Stmt)
  deriving Repr

infix:150 " ::= " => Stmt.assign
infixr:130 ";; "   => Stmt.seq

syntax "`[Expr|" term "]" : term

macro_rules
  | `(`[Expr|true])      => `((true : Expr))
  | `(`[Expr|false])     => `((false : Expr))
  | `(`[Expr|$n:num])    => `(($n : Expr))
  | `(`[Expr|$x:ident])  => `(($(Lean.quote x.getId.toString) : Expr))
  | `(`[Expr|$x = $y])   => `(Expr.bin `[Expr|$x] BinOp.eq `[Expr|$y])
  | `(`[Expr|$x && $y])  => `(Expr.bin `[Expr|$x] BinOp.and `[Expr|$y])
  | `(`[Expr|$x < $y])   => `(Expr.bin `[Expr|$x] BinOp.lt `[Expr|$y])
  | `(`[Expr|$x + $y])   => `(Expr.bin `[Expr|$x] BinOp.add `[Expr|$y])
  | `(`[Expr|$x - $y])   => `(Expr.bin `[Expr|$x] BinOp.sub `[Expr|$y])
  | `(`[Expr|!$x])       => `(Expr.una UnaryOp.not `[Expr|$x])
  | `(`[Expr|($x)])      => `(`[Expr|$x])

declare_syntax_cat stmt

syntax ident " := " term ";": stmt
syntax "if " "(" term ")" " {\n" stmt* "\n}" (" else " "{\n" stmt* "\n}")? : stmt
syntax "while " "(" term ")" "{\n" stmt* "\n}" : stmt

syntax "`[Stmt|" stmt* "]" : term

macro_rules
  | `(`[Stmt| ]) => `(Stmt.skip)
  | `(`[Stmt| $x:ident := $e:term;]) => `(Stmt.assign $(Lean.quote x.getId.toString) `[Expr| $e:term])
  | `(`[Stmt| if ($c) { $ts* } else { $es* }]) => `(Stmt.ite `[Expr| $c] `[Stmt| $ts*] `[Stmt| $es*])
  | `(`[Stmt| if ($c) { $ts* }]) => `(Stmt.ite `[Expr| $c] `[Stmt| $ts*] Stmt.skip)
  | `(`[Stmt| while ($c) { $b* }]) => `(Stmt.while `[Expr|$c] `[Stmt|$b*])
  | `(`[Stmt| $s $ss*]) => `(Stmt.seq `[Stmt|$s] `[Stmt|$ss*])

def example1 := `[Stmt|
  x := 8;
  y := 10;
  if (x < y) {
    x := x + 1;
  } else {
    y := y + 3;
  }
]

#reduce example1

def example2 := `[Stmt|
  x := 8;
  if (x < y) {
    x := x + 1;
  } else {
    y := y + 3;
    x := 9;
  }
  y := x;]

#eval example2

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

@[simp] theorem State.find?_update_self (σ : State) (x : Var) (v : Val) : (σ.update x v).find? x = some v := by
  match σ with -- TODO: automate this proof
  | [] => simp
  | (y, w) :: s =>
    simp
    split <;> simp [*]
    apply find?_update_self

@[simp] theorem State.find?_update (σ : State) (v : Val) (h : x ≠ z) : (σ.update x v).find? z = σ.find? z := by
  match σ with -- TODO: automate this proof
  | [] => simp [h.symm]
  | (y, w) :: σ =>
    simp
    split <;> simp [*]
    next hc => split <;> simp_all
    next =>
      split
      next => rfl
      next => exact find?_update σ v h

-- TODO: remove after we add better automation
@[simp] theorem State.find?_update' (σ : State) (v : Val) (h : z ≠ x) : (σ.update x v).find? z = σ.find? z :=
  State.find?_update σ v h.symm

theorem State.get_of_find? {σ : State} (h : σ.find? x = some v) : σ.get x = v := by
  simp [State.get, h, Option.getD]

@[simp] theorem State.find?_erase_self (σ : State) (x : Var) : (σ.erase x).find? x = none := by
  match σ with
  | [] => simp
  | (y, w) :: σ =>
    simp
    split <;> simp [*]
    next => exact find?_erase_self σ y
    next => exact find?_erase_self σ x

@[simp] theorem State.find?_erase (σ : State) (h : x ≠ z) : (σ.erase x).find? z = σ.find? z := by
  match σ with
  | [] => simp
  | (y, w) :: σ =>
    simp
    split <;> simp [*]
    next hxy => rw [hxy] at h; simp [h.symm]; exact find?_erase σ h
    next =>
      split
      next => rfl
      next => exact find?_erase σ h

-- TODO: remove after we add better automation
@[simp] theorem State.find?_erase' (σ : State) (h : z ≠ x) : (σ.erase x).find? z = σ.find? z :=
  State.find?_erase σ h.symm

syntax ident " ↦ " term : term

macro_rules
  | `($id:ident ↦ $v:term) => `(($(Lean.quote id.getId.toString), $v:term))

example : State.get [x ↦ .int 10, y ↦ .int 20] "x" = .int 10 := rfl

example : State.get [x ↦ 10, y ↦ 20] "x" = 10     := rfl
example : State.get [x ↦ 10, y ↦ true] "y" = true := rfl

@[simp] def Expr.eval (σ : State) : Expr → Option Val
  | val v   => some v
  | var x   => σ.get x
  | bin lhs op rhs => match lhs.eval σ, rhs.eval σ with
    | some v₁, some v₂ => op.eval v₁ v₂  -- BinOp.eval : BinOp → Val → Val → Option Val
    | _,       _       => none
  | una op arg => match arg.eval σ with
    | some v => op.eval v
    | _      => none


@[simp] def evalTrue  (c : Expr) (σ : State) : Prop := c.eval σ = some (Val.bool true)
@[simp] def evalFalse (c : Expr) (σ : State) : Prop := c.eval σ = some (Val.bool false)

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
  induction h₁ generalizing σ₂ <;> cases h₂ <;> try simp_all
  -- The rest of this proof should be automatic with congruence closure and a bit of forward reasoning
  case seq ih₁ ih₂ _ h₁ h₂ =>
    simp [ih₁ h₁] at ih₂
    simp [ih₂ h₂]
  case ifTrue ih h =>
    simp [ih h]
  case ifFalse ih h =>
    simp [ih h]
  case whileTrue ih₁ ih₂ h₁ h₂ =>
    simp [ih₁ h₁] at ih₂
    simp [ih₂ h₂]

abbrev EvalM := ExceptT String (StateM State)

def evalExpr (e : Expr) : EvalM Val := do
  match e.eval (← get) with
  | some v => return v
  | none => throw "failed to evaluate"

@[simp] def Stmt.eval (stmt : Stmt) (fuel : Nat := 100) : EvalM Unit := do
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

#eval `[Stmt| x := 3; y := 5; x := x + y;].eval |>.run {}
#eval `[Stmt| x := 0; while (true) { x := x + 1; }].eval |>.run {}

instance : Repr State where
  reprPrec a n :=
    match a, n with
    | [], _ => "[]"
    | as, _ =>
      let fs := as.map fun
        | (x, .int v)  => f!"{x} ↦ {v}"
        | (x, .bool v) => f!"{x} ↦ {v}"
      Std.Format.bracket "[" (Std.Format.joinSep fs ("," ++ Std.Format.line)) "]"

#eval `[Stmt| x := 3; y := 5; x := x + y; ].eval |>.run {}

@[simp] def BinOp.simplify : BinOp → Expr → Expr → Expr
  | .eq,  .val v₁,  .val  v₂ => .val (.bool (v₁ = v₂))
  | .and, .val (.bool a), .val (.bool b) => .val (.bool (a && b))
  | .lt,  .val (.int a),  .val (.int b)  => .val (.bool (a < b))
  | .add, .val (.int a), .val (.int b) => .val (.int (a + b))
  | .sub, .val (.int a), .val (.int b) => .val (.int (a - b))
  | op, a, b => .bin a op b

@[simp] def UnaryOp.simplify : UnaryOp → Expr → Expr
  | .not, .val (.bool b) => .val (.bool !b)
  | op, a => .una op a

@[simp] def Expr.simplify : Expr → Expr
  | bin lhs op rhs => op.simplify lhs.simplify rhs.simplify
  | una op arg => op.simplify arg.simplify
  | e => e

@[simp] theorem Expr.eval_simplify (e : Expr) : e.simplify.eval σ = e.eval σ := by
  induction e with simp
  | bin lhs op rhs ih_lhs ih_rhs =>
    simp [← ih_lhs, ← ih_rhs]
    split <;> simp [*]
  | una op arg ih_arg =>
    simp [← ih_arg]
    split <;> simp [*]

@[simp] def Stmt.simplify : Stmt → Stmt
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

def example3 := `[Stmt|
  if (1 < 2 + 3) {
    x := 3 + 1;
    y := y + x;
  } else {
    y := y + 3;
  }
]

#eval example3.simplify

theorem Stmt.simplify_correct (h : (σ, s) ⇓ σ') : (σ, s.simplify) ⇓ σ' := by
  induction h with simp_all
  | skip => exact Bigstep.skip
  | seq h₁ h₂ ih₁ ih₂ => exact Bigstep.seq ih₁ ih₂
  | assign => apply Bigstep.assign; simp [*]
  | whileTrue heq h₁ h₂ ih₁ ih₂ =>
    rw [← Expr.eval_simplify] at heq
    split
    next h => rw [h] at heq; simp at heq
    next hnp => simp [hnp] at ih₂; apply Bigstep.whileTrue heq ih₁ ih₂
  | whileFalse heq =>
    split
    next => exact Bigstep.skip
    next => apply Bigstep.whileFalse; simp [heq]
  | ifFalse heq h ih =>
    rw [← Expr.eval_simplify] at heq
    split <;> simp_all
    rw [← Expr.eval_simplify] at heq
    apply Bigstep.ifFalse heq ih
  | ifTrue heq h ih =>
    rw [← Expr.eval_simplify] at heq
    split <;> simp_all
    rw [← Expr.eval_simplify] at heq
    apply Bigstep.ifTrue heq ih

@[simp] def Expr.constProp (e : Expr) (σ : State) : Expr :=
  match e with
  | val v => v
  | var x => match σ.find? x with
    | some v => val v
    | none   => var x
  | bin lhs op rhs => bin (lhs.constProp σ) op (rhs.constProp σ)
  | una op arg => una op (arg.constProp σ)

@[simp] theorem Expr.constProp_nil (e : Expr) : e.constProp [] = e := by
  induction e <;> simp [*]

def State.length_erase_le (σ : State) (x : Var) : (σ.erase x).length ≤ σ.length := by
  match σ with
  | [] => simp
  | (y, v) :: σ =>
    by_cases hxy : x = y <;> simp [hxy]
    next => exact Nat.le_trans (length_erase_le σ y) (by simp_arith)
    next => simp_arith [length_erase_le σ x]

def State.length_erase_lt (σ : State) (x : Var) : (σ.erase x).length < σ.length.succ :=
  Nat.lt_of_le_of_lt (length_erase_le ..) (by simp_arith)

@[simp] def State.join (σ₁ σ₂ : State) : State :=
  match σ₁ with
  | [] => []
  | (x, v) :: σ₁ =>
    let σ₁' := erase σ₁ x -- Must remove duplicates. Alternative design: carry invariant that input state at constProp has no duplicates
    have : (erase σ₁ x).length < σ₁.length.succ := length_erase_lt ..
    match σ₂.find? x with
    | some w => if v = w then (x, v) :: join σ₁' σ₂ else join σ₁' σ₂
    | none => join σ₁' σ₂
termination_by _ σ₁ _ => σ₁.length

local notation "⊥" => []

@[simp] def Stmt.constProp (s : Stmt) (σ : State) : Stmt × State :=
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

theorem State.le_refl (σ : State) : σ ≼ σ :=
  fun _ _ h => h

theorem State.le_trans : σ₁ ≼ σ₂ → σ₂ ≼ σ₃ → σ₁ ≼ σ₃ :=
  fun h₁ h₂ x v h => h₂ (h₁ h)

theorem State.bot_le (σ : State) : ⊥ ≼ σ :=
  fun _ _ h => by contradiction

theorem State.erase_le_cons (h : σ' ≼ σ) : σ'.erase x ≼ ((x, v) :: σ) := by
  intro y w hf'
  by_cases hyx : y = x <;> simp [*] at hf' |-
  exact h hf'

theorem State.cons_le_cons (h : σ' ≼ σ) : (x, v) :: σ' ≼ (x, v) :: σ := by
  intro y w hf'
  by_cases hyx : y = x <;> simp [*] at hf' |-
  next => assumption
  next => exact h hf'

theorem State.cons_le_of_eq (h₁ : σ' ≼ σ) (h₂ : σ.find? x = some v) : (x, v) :: σ' ≼ σ := by
  intro y w hf'
  by_cases hyx : y = x <;> simp [*] at hf' |-
  next => assumption
  next => exact h₁ hf'

theorem State.erase_le (σ : State) : σ.erase x ≼ σ := by
  match σ with
  | [] => simp; apply le_refl
  | (y, v) :: σ =>
    simp
    split <;> try simp [*]
    next => apply erase_le_cons; apply le_refl
    next => apply cons_le_cons; apply erase_le

theorem State.join_le_left (σ₁ σ₂ : State) : σ₁.join σ₂ ≼ σ₁ := by
  match σ₁ with
  | [] => simp; apply le_refl
  | (x, v) :: σ₁ =>
    simp
    have : (erase σ₁ x).length < σ₁.length.succ := length_erase_lt ..
    have ih := join_le_left (State.erase σ₁ x) σ₂
    split
    next y w h =>
      split
      next => apply cons_le_cons; apply le_trans ih (erase_le _)
      next => apply le_trans ih (erase_le_cons (le_refl _))
    next h => apply le_trans ih (erase_le_cons (le_refl _))
termination_by _ σ₁ _ => σ₁.length

theorem State.join_le_left_of (h : σ₁ ≼ σ₂) (σ₃ : State) : σ₁.join σ₃ ≼ σ₂ :=
  le_trans (join_le_left σ₁ σ₃) h

theorem State.join_le_right (σ₁ σ₂ : State) : σ₁.join σ₂ ≼ σ₂ := by
  match σ₁ with
  | [] => simp; apply bot_le
  | (x, v) :: σ₁ =>
    simp
    have : (erase σ₁ x).length < σ₁.length.succ := length_erase_lt ..
    have ih := join_le_right (erase σ₁ x) σ₂
    split
    next y w h =>
      split <;> simp [*]
      next => apply cons_le_of_eq ih h
    next h => assumption
termination_by _ σ₁ _ => σ₁.length

theorem State.join_le_right_of (h : σ₁ ≼ σ₂) (σ₃ : State) : σ₃.join σ₁ ≼ σ₂ :=
  le_trans (join_le_right σ₃ σ₁) h

theorem State.eq_bot (h : σ ≼ ⊥) : σ = ⊥ := by
  match σ with
  | [] => simp
  | (y, v) :: σ =>
    have : State.find? ((y, v) :: σ) y = some v := by simp
    have := h this
    contradiction

theorem State.erase_le_of_le_cons (h : σ' ≼ (x, v) :: σ) : σ'.erase x ≼ σ := by
  intro y w hf'
  by_cases hxy : x = y <;> simp [*] at hf'
  have hf := h hf'
  simp [hxy, Ne.symm hxy] at hf
  assumption

theorem State.erase_le_update (h : σ' ≼ σ) : σ'.erase x ≼ σ.update x v := by
  intro y w hf'
  by_cases hxy : x = y <;> simp [*] at hf' |-
  exact h hf'

theorem State.update_le_update (h : σ' ≼ σ) : σ'.update x v ≼ σ.update x v := by
  intro y w hf
  induction σ generalizing σ' hf with
  | nil  => rw [eq_bot h] at hf; assumption
  | cons zw' σ ih =>
    have (z, w') := zw'; simp
    have : σ'.erase z ≼ σ := erase_le_of_le_cons h
    have ih := ih this
    revert ih hf
    split <;> simp [*] <;> by_cases hyz : y = z <;> simp (config := { contextual := true }) [*]
    next =>
      intro he'
      have he := h he'
      simp [*] at he
      assumption
    next =>
      by_cases hxy : x = y <;> simp [*]
      next => intros; assumption
      next =>
        intro he' ih
        exact ih he'

theorem Expr.eval_constProp_of_sub (e : Expr) (h : σ' ≼ σ) : (e.constProp σ').eval σ = e.eval σ := by
  induction e with simp [*]
  | var x =>
    split <;> simp
    next he => rw [State.get_of_find? (h he)]

theorem Expr.eval_constProp_of_eq_of_sub {e : Expr} (h₁ : e.eval σ = v) (h₂ : σ' ≼ σ) : (e.constProp σ').eval σ = v := by
  have := eval_constProp_of_sub e h₂
  simp [h₁] at this
  assumption

theorem Stmt.constProp_sub (h₁ : (σ₁, s) ⇓ σ₂) (h₂ : σ₁' ≼ σ₁) : (s.constProp σ₁').2 ≼ σ₂ := by
  induction h₁ generalizing σ₁' with simp
  | skip => assumption
  | assign heq =>
    split <;> simp
    next h =>
      have heq' := Expr.eval_constProp_of_eq_of_sub heq h₂
      rw [← Expr.eval_simplify, h] at heq'
      simp at heq'
      rw [heq']
      apply State.update_le_update h₂
    next h _ _ =>
      exact State.erase_le_update h₂
  | whileTrue heq h₃ h₄ ih₃ ih₄ =>
    have ih₃ := ih₃ h₂
    have ih₄ := ih₄ ih₃
    simp [heq] at ih₄
    exact ih₄
  | whileFalse heq => apply State.bot_le
  | ifTrue heq h ih =>
    have ih := ih h₂
    apply State.join_le_left_of ih
  | ifFalse heq h ih =>
    have ih := ih h₂
    apply State.join_le_right_of ih
  | seq h₃ h₄ ih₃ ih₄ => exact ih₄ (ih₃ h₂)

theorem Stmt.constProp_correct (h₁ : (σ₁, s) ⇓ σ₂) (h₂ : σ₁' ≼ σ₁) : (σ₁, (s.constProp σ₁').1) ⇓ σ₂ := by
  induction h₁ generalizing σ₁' with simp_all
  | skip => exact Bigstep.skip
  | assign heq =>
    split <;> simp
    next h =>
      have heq' := Expr.eval_constProp_of_eq_of_sub heq h₂
      rw [← Expr.eval_simplify, h] at heq'
      simp at heq'
      apply Bigstep.assign; simp [*]
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
    exact Bigstep.whileFalse heq
  | ifTrue heq h ih =>
    exact Bigstep.ifTrue (Expr.eval_constProp_of_eq_of_sub heq h₂) (ih h₂)
  | ifFalse heq h ih =>
    exact Bigstep.ifFalse (Expr.eval_constProp_of_eq_of_sub heq h₂) (ih h₂)

def Stmt.constPropagation (s : Stmt) : Stmt :=
  (s.constProp ⊥).1

theorem Stmt.constPropagation_correct (h : (σ, s) ⇓ σ') : (σ, s.constPropagation) ⇓ σ' :=
  constProp_correct h (State.bot_le _)

def example4 := `[Stmt|
  x := 2;
  if (x < 3) {
    x := x + 1;
    y := y + x;
  } else {
    y := y + 3;
  }
]

#eval example4.constPropagation.simplify

#exit
-- TODO: add simp theorems for monadic code
theorem Stmt.eval_correct {s : Stmt} (h : (s.eval fuel).run σ = (.ok unit, σ')) : (σ, s) ⇓ σ' := by
  induction fuel generalizing s σ σ' with simp at h
  | zero => injection h; contradiction
  | succ fuel ih =>
    split at h
    next => injection h with _ h; rw [h]; exact Bigstep.skip
    next => done

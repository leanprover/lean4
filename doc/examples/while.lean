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
  | assign   (x : Var) (e : Expr)
  | seq      (s₁ s₂ : Stmt)
  | ite      (c : Expr) (e t : Stmt)
  | «while»  (c : Expr) (b : Stmt)
  deriving Repr

infix:150 " ::= " => Stmt.assign
infixr:130 ";; "   => Stmt.seq

syntax "`[Expr|" term "]" : term

macro_rules
  | `(`[Expr|true])      => `((true : Expr))
  | `(`[Expr|false])     => `((false : Expr))
  | `(`[Expr|$n:numLit]) => `(($n : Expr))
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

@[simp] def State.update (s : State) (x : Var) (v : Val) : State :=
  match s with
  | [] => [(x, v)]
  | (y, w)::s => if x = y then (x, v)::s else (y, w) :: update s x v

@[simp] def State.get (s : State) (x : Var) : Val :=
  match s with
  | [] => .int 0
  | (y, v) :: s => if x = y then v else get s x

theorem State.get_update_self (s : State) (x : Var) (v : Val) : (s.update x v).get x = v := by
  match s with -- TODO: automate this proof
  | [] => simp
  | (y, w) :: s =>
    simp
    split <;> simp [*]
    apply get_update_self

theorem State.get_update (s : State) (x y : Var) (v : Val) (h : z ≠ x) : (s.update x v).get z = s.get z := by
  match s with -- TODO: automate this proof
  | [] => simp [h]; done
  | (y, w) :: s =>
    simp
    split <;> simp [*]
    next hc => split <;> simp_all
    next =>
      split
      next => rfl
      next => exact get_update s x y v h

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
  | whileTrue  : evalTrue c σ₁ → (σ₁, b) ⇓ σ₂ → (σ₂, .«while» c b) ⇓ σ₃ → (σ₁, .«while» c b) ⇓ σ₃
  | whileFalse : evalFalse c σ → (σ, .«while» c b) ⇓ σ

end

notation:60 "(" σ ", " s ")"  " ⇓ " σ':60 => Bigstep σ s σ'

/- This proof can be automated using forward reasoning. -/
theorem Bigstem.det (h₁ : (σ, s) ⇓ σ₁) (h₂ : (σ, s) ⇓ σ₂) : σ₁ = σ₂ := by
  induction h₁ generalizing σ₂ <;> cases h₂ <;> simp_all
  -- The rest of this proof should be automatic with congruence closure and a bit of forward reasoning
  case seq ih₁ ih₂ h₁ h₂ =>
    simp [ih₁ h₁] at ih₂
    simp [ih₂ h₂]
  case ifTrue ih _ h =>
    simp [ih h]
  case ifFalse ih _ h =>
    simp [ih h]
  case whileTrue ih₁ ih₂ _ h₁ h₂ =>
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
    | «while» c b =>
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
    split <;> simp
  | una op arg ih_arg =>
    simp [← ih_arg]
    split <;> simp

@[simp] def Stmt.simplify : Stmt → Stmt
  | skip => skip
  | assign x e => assign x e.simplify
  | seq s₁ s₂ => seq s₁.simplify s₂.simplify
  | ite c e t =>
    match c.simplify with
    | .val (.bool true) => e.simplify
    | .val (.bool false) => t.simplify
    | c' => ite c' e.simplify t.simplify
  | «while» c b =>
    match c.simplify with
    | .val (.bool false) => skip
    | c' => «while» c' b.simplify

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
    revert ih₂ -- This is a hack to make sure the next split simplify the two match expressions: TODO: make sure `simp` can do it
    split <;> intro ih₂
    next h => rw [h] at heq; simp at heq
    next h _ _ => rw [h] at heq; apply Bigstep.whileTrue heq ih₁ ih₂
  | whileFalse heq =>
    split
    next => exact Bigstep.skip
    next h _ _ => apply Bigstep.whileFalse; rw [← h]; simp [heq]
  | ifFalse heq h ih =>
    rw [← Expr.eval_simplify] at heq
    split <;> simp_all
    apply Bigstep.ifFalse heq ih
  | ifTrue heq h ih =>
    rw [← Expr.eval_simplify] at heq
    split <;> simp_all
    apply Bigstep.ifTrue heq ih

#exit
-- TODO: add simp theorems for monadic code
theorem Stmt.eval_correct {s : Stmt} (h : (s.eval fuel).run σ = (.ok unit, σ')) : (σ, s) ⇓ σ' := by
  induction fuel generalizing s σ σ' with simp at h
  | zero => injection h; contradiction
  | succ fuel ih =>
    split at h
    next => injection h with _ h; rw [h]; exact Bigstep.skip
    next => done

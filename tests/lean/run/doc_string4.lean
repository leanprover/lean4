/-!
# Arithmetic expressions for a simple imperative language.
-/

namespace imp
open tactic

/-- Variable names -/
@[reducible] def uname := string

/--
#brief Arithmetic expressions abstract syntax tree.

We encode x + 1 as
```
#check aexp.plus (aexp.var "x") (aexp.val 1)
```
-/
inductive aexp
| val  : nat → aexp
| var  : uname → aexp
| plus : aexp → aexp → aexp

/-- #brief Arithmetic expressions have decidable equality. -/
instance : decidable_eq aexp :=
by mk_dec_eq_instance

/-- #brief Value assigned to variables. -/
@[reducible] def value := nat

/-- #brief The state is a mapping from variable names to their values. -/
def state := uname → value

open aexp

/--
  #brief Given an arithmetic expression and a state, this function returns the
  value for the expression.

  ```
  example : aval (plus (val 3) (var "x")) (λ x, 0) = 3 :=
  rfl
  ```
  See [`aexp`](#imp.aexp)
-/
def aval : aexp → state → value
| (val n)      s := n
| (var x)      s := s x
| (plus a₁ a₂) s := aval a₁ s + aval a₂ s

/--
    #brief Update the state with then entry `x -> v`.
    We say we are assigning `v` to `x`.
-/
def updt (s : state) (x : uname) (v : value) : state :=
λ y, if x = y then v else s y

/--
  #brief  Very basic constant folding simplification procedure.
  For example, it reduces subexpressions such as (3 + 2) to 5.
-/
def asimp_const : aexp → aexp
| (val n)      := val n
| (var x)      := var x
| (plus a₁ a₂) :=
  match asimp_const a₁, asimp_const a₂ with
  | val n₁, val n₂ := val (n₁ + n₂)
  | b₁,     b₂     := plus b₁ b₂
  end

/-!
  _Remark_: we can prove by reflexivity the fact that the constant folder simplifies `(2+3)+x` into `5+x`.
  ```
  example : asimp_const (plus (plus (val 2) (val 3)) (var "x")) = plus (val 5) (var "x") :=
  rfl
  ```
-/

/-- #brief Prove that constant folding preserves the value of an artihmetic expressions. -/
lemma aval_asimp_const (a : aexp) (s : state) : aval (asimp_const a) s = aval a s :=
begin
  induction a with n x a₁ a₂ ih₁ ih₂,
  repeat {reflexivity},
  {unfold asimp_const aval,
   rewrite [-ih₁, -ih₂],
   cases (asimp_const a₁),
   repeat {cases (asimp_const a₂), repeat {reflexivity}}}
end

/--
  #brief Alternative proof without tactics that constant folding preserves
  the value of an arithmetic expression.

  This alternative proof is more verbose because we are essentially writing
  the proof term.
-/
lemma aval_asimp_const₂ : ∀ (a : aexp) (s : state), aval (asimp_const a) s = aval a s
| (val n) s := rfl
| (var x) s := rfl
| (plus a₁ a₂) s :=
  show aval (asimp_const (plus a₁ a₂)) s = aval a₁ s + aval a₂ s, from
  suffices aval (asimp_const._match_1 (asimp_const a₁) (asimp_const a₂)) s = aval (asimp_const a₁) s + aval (asimp_const a₂) s, from
    aval_asimp_const₂ a₁ s ▸ aval_asimp_const₂ a₂ s ▸ this,
  match asimp_const a₁, asimp_const a₂ with
  | val _,    val _    := rfl
  | val _,    var _    := rfl
  | val _,    plus _ _ := rfl
  | var _,    val _    := rfl
  | var _,    var _    := rfl
  | var _,    plus _ _ := rfl
  | plus _ _, val _    := rfl
  | plus _ _, var _    := rfl
  | plus _ _, plus _ _ := rfl
  end

/--
  #brief Alternative proof that mixes proof terms and tactics.

  See [`asimp_const`](#imp.asimp_const)
-/
lemma aval_asimp_const₃ : ∀ (a : aexp) (s : state), aval (asimp_const a) s = aval a s
| (val n) s := rfl
| (var x) s := rfl
| (plus a₁ a₂) s :=
  begin
   have h₁ := aval_asimp_const₃ a₁ s,
   have h₂ := aval_asimp_const₃ a₂ s,
   unfold asimp_const aval,
   rewrite [-h₁, -h₂],
   cases (asimp_const a₁); cases (asimp_const a₂); repeat {reflexivity}
  end

end imp

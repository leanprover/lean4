universes u v w

namespace quote_bas

inductive Expr (V : Type u)
| One {}            : Expr
| Var (v : V)       : Expr
| Mult (a b : Expr) : Expr

@[reducible] def Value := nat
def Env (V : Type u) := V → Value

open Expr

def evalExpr {V} (vs : Env V) : Expr V → Value
| One        := 1
| (Var v)    := vs v
| (Mult a b) := evalExpr a * evalExpr b

def novars : Env empty :=
empty.rec _

def singlevar (x : Value) : Env unit :=
λ _, x

open sum

def merge {A : Type u} {B : Type v} (a : Env A) (b : Env B) : Env (sum A B)
| (inl j) := a j
| (inr j) := b j

def map_var {A : Type u} {B : Type v} (f : A → B) : Expr A → Expr B
| One        := One
| (Var v)    := Var (f v)
| (Mult a b) := Mult (map_var a) (map_var b)

def sum_assoc {A : Type u} {B : Type v} {C : Type w} : sum (sum A B) C → sum A (sum B C)
| (inl (inl a)) := inl a
| (inl (inr b)) := inr (inl b)
| (inr c)       := inr (inr c)

attribute [simp] evalExpr map_var sum_assoc merge

@[simp] lemma eval_map_var_shift {A : Type u} {B : Type v} (v : Env A) (v' : Env B) (e : Expr A) : evalExpr (merge v v') (map_var inl e) = evalExpr v e :=
begin
  induction e,
  reflexivity,
  reflexivity,
  simp [*]
end

@[simp] lemma eval_map_var_sum_assoc {A : Type u} {B : Type v} {C : Type w} (v : Env A) (v' : Env B) (v'' : Env C) (e : Expr (sum (sum A B) C)) :
                             evalExpr (merge v (merge v' v'')) (map_var sum_assoc e) = evalExpr (merge (merge v v') v'') e :=
begin
  induction e,
  reflexivity,
  { cases e with v₁, cases v₁, all_goals {simp} },
  { simp [*] }
end

class Quote {V : out_param $ Type u} (l : out_param $ Env V) (n : Value) {V' : out_param $ Type v} (r : out_param $ Env V') :=
(quote      : Expr (sum V V'))
(eval_quote : evalExpr (merge l r) quote = n)

export Quote (quote eval_quote)
attribute [simp] eval_quote

instance quote_one (V) (v : Env V) : Quote v 1 novars :=
{ quote      := One,
  eval_quote := rfl }

instance quote_mul {V : Type u} (v : Env V) (n) {V' : Type v} (v' : Env V') (m) {V'' : Type w} (v'' : Env V'')
                   [Quote v n v'] [Quote (merge v v') m v''] :
                   Quote v (n * m) (merge v' v'') :=
{ quote      := Mult (map_var sum_assoc (map_var inl (quote n))) (map_var sum_assoc (quote m)),
  eval_quote := by simp }

end quote_bas

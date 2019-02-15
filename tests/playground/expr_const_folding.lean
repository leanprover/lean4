inductive Expr
| Var : nat → Expr
| Val : nat → Expr
| Add : Expr → Expr → Expr
| Mul : Expr → Expr → Expr

open Expr nat

def mk_expr : nat → nat → Expr
| 0     v := if v = 0 then Var 1 else Val v
| (n+1) v := Add (mk_expr n (v+1)) (mk_expr n (v-1))

def append_add : Expr → Expr → Expr
| (Add e₁ e₂) e₃ := Add e₁ (append_add e₂ e₃)
| e₁          e₂ := Add e₁ e₂

def append_mul : Expr → Expr → Expr
| (Mul e₁ e₂) e₃ := Mul e₁ (append_mul e₁ e₂)
| e₁          e₂ := Mul e₁ e₂

def reassoc : Expr → Expr
| (Add e₁ e₂) :=
  let e₁' := reassoc e₁ in
  let e₂' := reassoc e₂ in
  append_add e₁' e₂'
| (Mul e₁ e₂) :=
  let e₁' := reassoc e₁ in
  let e₂' := reassoc e₂ in
  append_mul e₁' e₂'
| e := e

def const_folding : Expr → Expr
| (Add e₁ e₂) :=
  let e₁ := const_folding e₁ in
  let e₂ := const_folding e₂ in
  (match e₁, e₂ with
   | Val a, Val b         := Val (a+b)
   | Val a, Add e (Val b) := Add (Val (a+b)) e
   | Val a, Add (Val b) e := Add (Val (a+b)) e
   | _,     _             := Add e₁ e₂)
| (Mul e₁ e₂) :=
  let e₁ := const_folding e₂ in
  let e₁ := const_folding e₂ in
  (match e₁, e₂ with
   | Val a, Val b         := Val (a*b)
   | Val a, Mul e (Val b) := Mul (Val (a*b)) e
   | Val a, Mul (Val b) e := Mul (Val (a*b)) e
   | _,     _             := Mul e₁ e₂)
| e         := e

def size : Expr → nat
| (Add l r) := size l + size r + 1
| (Mul l r) := size l + size r + 1
| e         := 1

def to_string_aux : Expr → string → string
| (Var v)     r := r ++ "#" ++ to_string v
| (Val v)     r := r ++ to_string v
| (Add e₁ e₂) r := (to_string_aux e₂ ((to_string_aux e₁ (r ++ "(")) ++ " + ")) ++ ")"
| (Mul e₁ e₂) r := (to_string_aux e₂ ((to_string_aux e₁ (r ++ "(")) ++ " * ")) ++ ")"

def eval : Expr → nat
| (Var x) := 0
| (Val v) := v
| (Add l r) := eval l + eval r
| (Mul l r) := eval l * eval r

def main : io uint32 :=
let e  := (mk_expr 23 1) in
let v₁ := eval e in
let v₂ := eval (const_folding (reassoc e)) in
io.println' (to_string v₁ ++ " " ++ to_string v₂) *>
pure 0

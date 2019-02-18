data Expr = Var Integer
  | Val Integer
  | Add Expr Expr
  | Mul Expr Expr

mk_expr :: Integer -> Integer -> Expr
mk_expr 0 v = if v == 0 then Var 1 else Val v
mk_expr n v = Add (mk_expr (n-1) (v+1)) (mk_expr (n-1) (max (v-1) 0))

append_add :: Expr -> Expr -> Expr
append_add (Add e₁ e₂) e₃ = Add e₁ (append_add e₂ e₃)
append_add e₁          e₂ = Add e₁ e₂

append_mul :: Expr -> Expr -> Expr
append_mul (Mul e₁ e₂) e₃  = Mul e₁ (append_mul e₂ e₃)
append_mul e₁          e₂ = Mul e₁ e₂

reassoc :: Expr -> Expr
reassoc (Add e₁ e₂) =
  let e₁' = reassoc e₁ in
  let e₂' = reassoc e₂ in
  append_add e₁' e₂'
reassoc (Mul e₁ e₂) =
  let e₁' = reassoc e₁ in
  let e₂' = reassoc e₂ in
  append_mul e₁' e₂'
reassoc e = e

const_folding :: Expr -> Expr
const_folding (Add e₁ e₂) =
  let e₁' = const_folding e₁ in
  let e₂' = const_folding e₂ in
  (case (e₁', e₂') of
     (Val a, Val b        ) -> Val (a+b)
     (Val a, Add e (Val b)) -> Add (Val (a+b)) e
     (Val a, Add (Val b) e) -> Add (Val (a+b)) e
     (_,     _            ) -> Add e₁' e₂')
const_folding (Mul e₁ e₂) =
  let e₁' = const_folding e₁ in
  let e₂' = const_folding e₂ in
  (case (e₁', e₂') of
     (Val a, Val b        ) -> Val (a*b)
     (Val a, Mul e (Val b)) -> Mul (Val (a*b)) e
     (Val a, Mul (Val b) e) -> Mul (Val (a*b)) e
     (_,     _            ) -> Mul e₁' e₂')
const_folding e         = e

eval :: Expr -> Integer
eval (Var _) = 0
eval (Val v) = v
eval (Add l r) = eval l + eval r
eval (Mul l r) = eval l * eval r

main :: IO ()
main =
  let e  = (mk_expr 23 1) in
  let v₁ = eval e in
  let v₂ = eval (const_folding (reassoc e)) in
  putStrLn (show v₁ ++ " " ++ show v₂)

data Expr =
    Val Int
  | Var String
  | Add Expr Expr
  | Mul Expr Expr
  | Pow Expr Expr
  | Ln  Expr

pown :: Int -> Int -> Int
pown a 0 = 1
pown a 1 = a
pown a n =
  let b = pown a (n `div` 2) in
  b * b * (if n `mod` 2 == 0 then 1 else a)

add :: Expr -> Expr -> Expr
add (Val n)   (Val m)         = Val (n + m)
add (Val 0)   f               = f
add f         (Val 0)         = f
add f         (Val n)         = add (Val n) f
add (Val n)   (Add (Val m) f) = add (Val (n+m)) f
add f         (Add (Val n) g) = add (Val n) (add f g)
add (Add f g) h               = add f (add g h)
add f         g               = Add f g

mul :: Expr -> Expr -> Expr
mul (Val n)   (Val m)         = Val (n*m)
mul (Val 0)   _               = Val 0
mul _         (Val 0)         = Val 0
mul (Val 1)   f               = f
mul f         (Val 1)         = f
mul f         (Val n)         = mul (Val n) f
mul (Val n)   (Mul (Val m) f) = mul (Val (n*m)) f
mul f         (Mul (Val n) g) = mul (Val n) (mul f g)
mul (Mul f g) h               = mul f (mul g h)
mul f         g               = Mul f g

pow :: Expr -> Expr -> Expr
pow (Val m) (Val n) = Val (pown m n)
pow _       (Val 0) = Val 1
pow f       (Val 1) = f
pow (Val 0) _       = Val 0
pow f       g       = Pow f g

ln :: Expr -> Expr
ln (Val 1) = Val 0
ln f       = Ln f

d :: String -> Expr -> Expr
d x (Val _)   = Val 0
d x (Var y)   = if x == y then Val 1 else Val 0
d x (Add f g) = add (d x f) (d x g)
d x (Mul f g) = add (mul f (d x g)) (mul g (d x f))
d x (Pow f g) = mul (pow f g) (add (mul (mul g (d x f)) (pow f (Val (-1)))) (mul (ln f) (d x g)))
d x (Ln f)    = mul (d x f) (pow f (Val (-1)))

count :: Expr -> Integer
count (Val _) = 1
count (Var _) = 1
count (Add f g) = count f + count g
count (Mul f g) = count f + count g
count (Pow f g) = count f + count g
count (Ln f)    = count f

nest_aux :: Int -> (Int -> Expr -> IO Expr) -> Int -> Expr -> IO Expr
nest_aux s f 0 x = pure x
nest_aux s f m x = f (s - m) x >>= nest_aux s f (m-1)

nest f n e = nest_aux n f n e

deriv :: Int -> Expr -> IO Expr
deriv i f = do
  let f' = d "x" f
  putStrLn (show (i+1) ++ " count: " ++ (show $ count f'))
  pure f'

main = do
  let x = Var "x"
  let f = pow x x
  nest deriv 10 f

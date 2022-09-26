import System.Environment

data Color =
  Red | Black

data Tree =
  Leaf
  | Node Color Tree Int Bool Tree

fold :: (Int -> Bool -> σ -> σ) -> Tree -> σ -> σ
fold _ Leaf b               = b
fold f (Node _ l k v r)   b = fold f r (f k v (fold f l b))

balance1 :: Int -> Bool -> Tree -> Tree -> Tree
balance1 kv vv t (Node _ (Node Red l kx vx r₁) ky vy r₂) = Node Red (Node Black l kx vx r₁) ky vy (Node Black r₂ kv vv t)
balance1 kv vv t (Node _ l₁ ky vy (Node Red l₂ kx vx r)) = Node Red (Node Black l₁ ky vy l₂) kx vx (Node Black r kv vv t)
balance1 kv vv t (Node _ l  ky vy r)                     = Node Black (Node Red l ky vy r) kv vv t
balance1 _  _  _ _                                       = Leaf

balance2 :: Int -> Bool -> Tree -> Tree -> Tree
balance2 kv vv t (Node _ (Node Red l kx₁ vx₁ r₁) ky vy r₂)  = Node Red (Node Black t kv vv l) kx₁ vx₁ (Node Black r₁ ky vy r₂)
balance2 kv vv t (Node _ l₁ ky vy (Node Red l₂ kx₂ vx₂ r₂)) = Node Red (Node Black t kv vv l₁) ky vy (Node Black l₂ kx₂ vx₂ r₂)
balance2 kv vv t (Node _ l ky vy r)                         = Node Black t kv vv (Node Red l ky vy r)
balance2 _  _  _ _                                          = Leaf

is_red :: Tree -> Bool
is_red (Node Red _ _ _ _) = True
is_red _                  = False

ins :: Tree -> Int -> Bool -> Tree
ins Leaf                 kx vx = Node Red Leaf kx vx Leaf
ins (Node Red a ky vy b) kx vx =
   (if kx < ky then Node Red (ins a kx vx) ky vy b
    else if ky < kx then Node Red a ky vy (ins b kx vx)
    else Node Red a ky vy (ins b kx vx))
ins (Node Black a ky vy b) kx vx =
    if kx < ky then
      (if is_red a then balance1 ky vy b (ins a kx vx)
       else Node Black (ins a kx vx) ky vy b)
    else if ky < kx then
      (if is_red b then balance2 ky vy a (ins b kx vx)
       else Node Black a ky vy (ins b kx vx))
    else Node Black a kx vx b

set_black :: Tree -> Tree
set_black (Node _ l k v r) = Node Black l k v r
set_black e                = e

insert t k v =
  if is_red t then set_black (ins t k v)
  else ins t k v

mk_Map_aux :: Int -> Tree -> Tree
mk_Map_aux 0 m = m
mk_Map_aux n m = let n' = n-1 in mk_Map_aux n' (insert m n' (n' `mod` 10 == 0))

mk_Map n = mk_Map_aux n Leaf

main = do
  [arg] <- getArgs
  let m = mk_Map $ read arg
  let v = fold (\_ v r -> if v then r + 1 else r) m 0
  print v

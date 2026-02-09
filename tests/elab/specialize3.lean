class Class where
instance empty: Class := {}

mutual
inductive T (δ: Class) where
| mk (ss: List (S δ))

inductive S (δ: Class) where
| mk (ts: List (T δ))
end

mutual
partial def str_T: T δ → String
| .mk ss => "\n".intercalate (ss.map str_S)

partial def str_S: S δ → String
| .mk ts => "\n".intercalate (ts.map str_T)
end

def error := str_T (T.mk (δ := empty) [])

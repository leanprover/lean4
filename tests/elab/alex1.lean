universe u

/-- A curried function of exactly `n` arguments; `α → ... → α → β` -/
abbrev CurriedFun (α β : Type u) : Nat → Type u
  | 0   => β
  | n+1 => α → CurriedFun α β n

/-- A curried type function of `n` arguments, i.e., `Type u → Type u → ... → Type u` -/
abbrev CurriedTypeFun : Nat → Type (u+1)
  := CurriedFun (Type u) (Type u)

/-- In my actual code, `GenTypeFun` is distinct from `CurriedTypeFun`, and `m` is used -/
abbrev GenTypeFun (n m : Nat) : Type _
  := CurriedFun (Type u) (Type u) n

def asCurried {n m : Nat} (F : GenTypeFun n m) : CurriedTypeFun (m + n)
  := match n, m with
      | 0,   _    => by sorry
      | _,   0    => by sorry
      | n+1, _    => fun τ => asCurried (F τ)

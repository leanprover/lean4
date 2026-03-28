inductive MyBool where
  | MyTrue
  | MyFalse

inductive T where
  | mk (b: MyBool) (u: Unit)

inductive isTrue: T → Type where
  | intro: isTrue (.mk .MyTrue ())

example {τ: T} (h: isTrue τ): Unit :=
  match τ, h with
  | .mk .MyTrue (), .intro => ()

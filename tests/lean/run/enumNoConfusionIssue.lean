inductive MyBool :=
  | MyTrue
  | MyFalse

inductive T :=
  | mk (b: MyBool) (u: Unit)

inductive isTrue: T → Type :=
  | intro: isTrue (.mk .MyTrue ())

example {τ: T} (h: isTrue τ): Unit :=
  match τ, h with
  | .mk .MyTrue (), .intro => ()

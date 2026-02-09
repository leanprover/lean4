inductive T
  | t : T

@[reducible] def T.eval : T → Type
  | T.t => Int

def T.default (τ : T) : τ.eval :=
  match τ, τ.eval with
  | T.t, .(Int) => (0 : Int)

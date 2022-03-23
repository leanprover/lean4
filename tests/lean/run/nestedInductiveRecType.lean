namespace Ex1

inductive T :=
  | int : Int -> T
  | tuple : List T -> T

@[reducible] def T.eval (t : T) : Type :=
  @T.rec
    (motive_1 := fun _ => Type)
    (motive_2 := fun _ => Type)
    (fun _ => Int)
    (fun _ ih => ih)
    Unit
    (fun _ _ ih₁ ih₂ => ih₁ × ih₂)
    t

@[reducible] def T.evalList (t : List T) : Type :=
  @T.rec_1
    (motive_1 := fun _ => Type)
    (motive_2 := fun _ => Type)
    (fun _ => Int)
    (fun _ ih => ih)
    Unit
    (fun _ _ ih₁ ih₂ => ih₁ × ih₂)
    t

mutual
  def T.default (τ : T): τ.eval :=
    match τ with
    | T.int v => v
    | T.tuple τs => defaultList τs

  def T.defaultList (τs : List T) : T.evalList τs :=
    match τs with
    | []    => ()
    | τ::τs => (τ.default, defaultList τs)
end

#eval T.default (.int 5) -- 5
#eval T.default (.tuple [.int 5]) -- (5, ())
#eval T.default (.tuple [.int 5, .int 6]) -- (5, 6, ())

end Ex1

namespace Ex2

inductive T :=
  | int : Int -> T
  | tuple : List T -> T

@[reducible] def T.eval (t : T) : Type :=
  @T.rec
    (motive_1 := fun _ => Type)
    (motive_2 := fun _ => Type)
    (fun _ => Int)
    (fun _ ih => ih)
    Unit
    (fun _ τs ih₁ ih₂ =>
      match τs with
      | [] => ih₁
      | _  => ih₁ × ih₂)
    t

@[reducible] def T.evalList (t : List T) : Type :=
  @T.rec_1
    (motive_1 := fun _ => Type)
    (motive_2 := fun _ => Type)
    (fun _ => Int)
    (fun _ ih => ih)
    Unit
    (fun _ τs ih₁ ih₂ =>
      match τs with
      | [] => ih₁
      | _  => ih₁ × ih₂)
    t

mutual
  def T.default (τ : T): τ.eval :=
    match τ with
    | T.int v => v
    | T.tuple τs => defaultList τs

  def T.defaultList (τs : List T) : T.evalList τs :=
    match τs with
    | []    => ()
    | [τ]   => τ.default
    | τ₁::τ₂::τs => (τ₁.default, defaultList (τ₂::τs))
end

#eval T.default (.int 5) -- 5
#eval T.default (.tuple [.int 5]) -- 5
#eval T.default (.tuple [.int 5, .int 6]) -- (5, 6)

end Ex2

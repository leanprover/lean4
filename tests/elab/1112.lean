mutual
    inductive Lift : Bool -> Type -> Type 2

    inductive Env : List Bool -> Type 2
    | cons : Lift t y -> Env [t]
end

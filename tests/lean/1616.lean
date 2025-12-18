inductive Cover : (x y z : List α) -> Type u
  | done  : Cover [] [] []
  | left  : Cover x y z -> Cover (t :: x) y (t :: z)
  | right : Cover x y z -> Cover x (t :: y) (t :: z)
  | both  : Cover x y z -> Cover (t :: x) (t :: y) (t :: z)

inductive Linear : Cover x y z -> Prop
  | done : Linear .done
  | left : Linear c -> Linear (.left c)
  | right : Linear c -> Linear (.right c)

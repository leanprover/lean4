namespace Value

inductive Primitive where
  | Bool (b : Bool)
  | Int (i : Int)
  | String (s : String)

deriving instance DecidableEq for Primitive -- Works

inductive Value where
  | Primitive (p : Primitive)

deriving instance DecidableEq for Primitive -- (no longer) fails
deriving instance DecidableEq for _root_.Value.Primitive -- (no longer) fails

deriving instance Repr for Primitive
deriving instance Repr for _root_.Value.Primitive

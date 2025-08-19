
/-!
Checks if derived instances refer to inductives correct even in tricky
namespace situations
-/

namespace Value

inductive Primitive where
  | Bool (b : Bool)
  | Int (i : Int)
  | String (s : String)

deriving instance DecidableEq for Primitive -- Works

inductive Value where
  | Primitive (p : Primitive)

deriving instance BEq for Primitive -- (no longer) fails
deriving instance Repr for _root_.Value.Primitive -- (no longer) fails

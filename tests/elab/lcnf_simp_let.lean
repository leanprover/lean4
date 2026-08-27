class OMonad (W : Type u → Type v) where

class MonadTrans (T : (Type _ → Type _) → (Type _ → Type _)) where

instance [OMonad m] [MonadTrans T] : OMonad (T m) where

instance : OMonad Id where

instance : MonadTrans (StateT σ) where

class LawfulOMonad (W) [OMonad W] where

instance : LawfulOMonad (StateT σ Id) where

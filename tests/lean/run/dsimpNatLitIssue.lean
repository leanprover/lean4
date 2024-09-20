variable {R M : Type}

/-- Typeclass for the `⊥` (`\bot`) notation -/
class Bot (α : Type) where
  /-- The bot (`⊥`, `\bot`) element -/
  bot : α

/-- The bot (`⊥`, `\bot`) element -/
notation "⊥" => Bot.bot

/-- Typeclass for types with a scalar multiplication operation, denoted `•` (`\bu`) -/
class SMul (M α : Type) where
  smul : M → α → α

infixr:73 " • " => SMul.smul

structure Submodule (R : Type) (M : Type) [Zero M] [SMul R M] where
  carrier : M → Prop
  zero_mem : carrier (0 : M)

variable [Zero M] [SMul R M]

instance : Bot (Submodule R M) where
  bot := ⟨(· = 0), rfl⟩

instance : Zero (Submodule R M) where
  zero := ⊥

@[simp]
theorem zero_eq_bot : (0 : Submodule R M) = ⊥ :=
  rfl

theorem ohai : (0 : Submodule R M) = ⊥ := by
  simp -- works

theorem oops : (0 : Submodule R M) = ⊥ := by
  dsimp -- should work

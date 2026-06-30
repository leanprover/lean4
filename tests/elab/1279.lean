inductive O
| int
| real
| bool
| unit
deriving Inhabited, BEq, Repr

-- only `Arrow.id` and `Arrow.comp` really matter for my problem
inductive Arrow : (_dom _cod : O) → Type
  -- identity
  | id : {α : O} → Arrow α α

  -- `α → α` arrows
  | unit : Arrow O.unit O.unit
  | not : Arrow O.bool O.bool
  | succᵢ : Arrow O.int O.int
  | succᵣ : Arrow O.real O.real

  | comp {α β γ} : Arrow β γ → Arrow α β → Arrow α γ

  -- `unit → bool`
  | tru : Arrow O.unit O.bool
  | fls : Arrow O.unit O.bool
  -- `unit → int`
  | zero : Arrow O.unit O.int
  -- `int → bool`
  | isZero : Arrow O.int O.bool
  -- `int → real`
  | toReal : Arrow O.int O.real
deriving Repr

def Arrow.compose₁ {α β γ : O} :
  Arrow β γ
  → Arrow α β
  → Arrow α γ
-- id.compose₁ g = g
| id, g => g
-- f.compose₁ id = f
| f, id => f
-- else
| comp f₁ f₂, g => comp f₁ (comp f₂ g)
| f, g => comp f g

#print Arrow.compose₁
-- def Arrow.compose₁ : {α β γ : O} → Arrow β γ → Arrow α β → Arrow α γ :=
-- fun {α β γ} x x_1 =>
--   match β, γ, x, x_1 with
--   | β, .(β), Arrow.id, g => g
--   | .(α), γ, f, Arrow.id => f
--   | β, γ, Arrow.comp f₁ f₂, g => Arrow.comp f₁ (Arrow.comp f₂ g)
--   | β, γ, f, g => Arrow.comp f g
#eval Arrow.compose₁ Arrow.unit Arrow.id
-- Arrow.comp (Arrow.unit) (Arrow.id) -- Error: it should be `Arrow.unit`

example : Arrow.compose₁ .id .id         = (.id (α := o)) := rfl
example : Arrow.compose₁ .id .unit       = .unit          := rfl
example : Arrow.compose₁ .id (.comp f g) = .comp f g      := rfl
example : Arrow.compose₁ .unit       .id = .unit := rfl
example : Arrow.compose₁ (.comp f g) .id = .comp f g := rfl
example : Arrow.compose₁ .unit .unit = .comp .unit .unit := rfl
example : Arrow.compose₁ (.comp f g) .unit = .comp f (.comp g .unit) := rfl
example : Arrow.compose₁ .unit (.comp f g) = .comp .unit (.comp f g) := rfl

theorem ex_1 : Arrow.compose₁ f .id = f := by
  cases f <;> simp!

theorem ex_2 : Arrow.compose₁ f .id = f := by
  cases f <;> simp!

theorem ex_3 : Arrow.compose₁ .id f = f := by
  cases f <;> simp!

theorem ex_4 : h ≠ .id → Arrow.compose₁ (.comp f g) h = .comp f (.comp g h) := by
  intros
  cases h <;> simp_all!

def Arrow.isId : Arrow dom com → Prop
  | .id => True
  | _ => False

def Arrow.isComp : Arrow dom com → Prop
  | .comp .. => True
  | _ => False

theorem ex_5 (f : Arrow β γ) (g : Arrow α β) : ¬ f.isId → ¬ g.isId → ¬ f.isComp → Arrow.compose₁ f g = .comp f g := by
  intros
  cases f <;> cases g <;> simp_all!

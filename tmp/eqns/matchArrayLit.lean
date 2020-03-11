universes u

inductive ArrayLitMatch (α : Type u)
| sz0 {}             : ArrayLitMatch
| sz1 (a₁ : α)       : ArrayLitMatch
| sz2 (a₁ a₂ : α)    : ArrayLitMatch
| sz3 (a₁ a₂ a₃ : α) : ArrayLitMatch
| other {}           : ArrayLitMatch

def matchArrayLit {α : Type u} (a : Array α) : ArrayLitMatch α :=
if 0 = a.size then
  ArrayLitMatch.sz0
else if h : 1 = a.size then
  ArrayLitMatch.sz1 (a.getLit 0 h (ofDecideEqTrue rfl))
else if h : 2 = a.size then
  ArrayLitMatch.sz2 (a.getLit 0 h (ofDecideEqTrue rfl)) (a.getLit 1 h (ofDecideEqTrue rfl))
else if h : 3 = a.size then
  ArrayLitMatch.sz3 (a.getLit 0 h (ofDecideEqTrue rfl)) (a.getLit 1 h (ofDecideEqTrue rfl)) (a.getLit 2 h (ofDecideEqTrue rfl))
else
  ArrayLitMatch.other

def matchArrayLit.eq0 {α : Type u} : matchArrayLit (#[] : Array α) = ArrayLitMatch.sz0 :=
rfl

def matchArrayLit.eq1 {α : Type u} (a₁ : α) : matchArrayLit #[a₁] = ArrayLitMatch.sz1 a₁ :=
rfl

def matchArrayLit.eq2 {α : Type u} (a₁ a₂ : α) : matchArrayLit #[a₁, a₂] = ArrayLitMatch.sz2 a₁ a₂ :=
rfl

def matchArrayLit.eq3 {α : Type u} (a₁ a₂ a₃ : α) : matchArrayLit #[a₁, a₂, a₃] = ArrayLitMatch.sz3 a₁ a₂ a₃ :=
rfl

def matchArrayLit.eq4 {α : Type u} (a₁ a₂ a₃ a₄ : α) : matchArrayLit #[a₁, a₂, a₃, a₄] = ArrayLitMatch.other :=
rfl

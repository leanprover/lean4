inductive L (α : Type u) : Type u where
  | nil : L α
  | cons (x : α) (xs : L α) : L α

/--
info: @[reducible] def L.nil.noConfusion.{u_1, u} : {α : Type u} → (P : Sort u_1) → L.nil = L.nil → P → P
-/
#guard_msgs in
#print sig L.nil.noConfusion

/--
info: @[reducible] def L.cons.noConfusion.{u_1, u} : {α : Type u} →
  (P : Sort u_1) →
    (x : α) → (xs : L α) → (x' : α) → (xs' : L α) → L.cons x xs = L.cons x' xs' → (x = x' → xs = xs' → P) → P
-/
#guard_msgs in
#print sig L.cons.noConfusion

inductive Vec (α : Type u) : Nat → Type u where
  | nil : Vec α 0
  | cons : {n : Nat} → (x : α) → (xs : Vec α n) → Vec α (n + 1)

/--
info: @[reducible] def Vec.cons.noConfusion.{u_1, u} : {α : Type u} →
  (P : Sort u_1) →
    {n : Nat} →
      (x : α) →
        (xs : Vec α n) → (x' : α) → (xs' : Vec α n) → Vec.cons x xs = Vec.cons x' xs' → (x = x' → xs = xs' → P) → P
-/
#guard_msgs in
#print sig Vec.cons.noConfusion

inductive I : (n : Nat) → Type where
  | mk n : (b : Bool) → I (n / 2)

/--
info: @[reducible] def I.mk.noConfusion.{u} : (P : Sort u) →
  (n : Nat) → (b b' : Bool) → I.mk n b = I.mk n b' → (b = b' → P) → P
-/
#guard_msgs in #print sig I.mk.noConfusion


inductive WithDep {α : Type u} (β : α → Type v) : Type (max u v) where
  | intro (a : α) (b : β a) : WithDep β

/--
info: @[reducible] def WithDep.intro.noConfusion.{u_1, u, v} : {α : Type u} →
  {β : α → Type v} →
    (P : Sort u_1) →
      (a : α) → (b : β a) → (a' : α) → (b' : β a') → WithDep.intro a b = WithDep.intro a' b' → (a = a' → b ≍ b' → P) → P
-/
#guard_msgs in #print sig WithDep.intro.noConfusion

-- Copy of 3386
-- This is a tricky case: `Tmₛ {T1 A1} a1 arg1 = Tmₛ {T2 A2} a2 arg2` only type checks if
-- `A1 = A2` and `arg1 = arg1`. The latter requires `T1 = T2`, even though `T` does not seem to
-- appear in the result type of `Tmₐ.app`.

inductive Tyₛ : Type (u+1)
| SPi : (T : Type u) -> (T -> Tyₛ) -> Tyₛ

/--
info: @[reducible] def Tyₛ.SPi.noConfusion.{u_1, u} : (P : Sort u_1) →
  (T : Type u) →
    (a : T → Tyₛ) → (T' : Type u) → (a' : T' → Tyₛ) → Tyₛ.SPi T a = Tyₛ.SPi T' a' → (T = T' → a ≍ a' → P) → P
-/
#guard_msgs in #print sig Tyₛ.SPi.noConfusion

inductive Tmₛ.{u} : Tyₛ.{u} -> Type (u+1)
| app : Tmₛ (.SPi T A) -> (arg : T) -> Tmₛ (A arg)

set_option pp.explicit true in
/--
info: constructor Tmₛ.app.{u} : {T : Type u} → {A : T → Tyₛ} → Tmₛ (Tyₛ.SPi T A) → (arg : T) → Tmₛ (A arg)
-/
#guard_msgs in
#print sig Tmₛ.app


/--
info: @[reducible] def Tmₛ.app.noConfusion.{u_1, u} : (P : Sort u_1) →
  {T : Type u} →
    {A : T → Tyₛ} →
      (a : Tmₛ (Tyₛ.SPi T A)) → (arg : T) → (a' : Tmₛ (Tyₛ.SPi T A)) → a.app arg = a'.app arg → (a = a' → P) → P :=
fun P {T} {A} a arg a' h k => Tmₛ.noConfusion h fun T_eq A_eq a_eq arg_eq => k ⋯
-/
#guard_msgs in #print Tmₛ.app.noConfusion


unsafe inductive U : Type | mk : (U → U) → U

/--
info: @[reducible] unsafe def U.mk.noConfusion.{u} : (P : Sort u) → (a a' : U → U) → U.mk a = U.mk a' → (a = a' → P) → P
-/
#guard_msgs in #print sig U.mk.noConfusion

-- More tests suggested by Claude

-- Test 2: Indexed family with complex indices
inductive Matrix (α : Type u) : Nat → Nat → Type u where
  | empty : Matrix α 0 0
  | row (n m : Nat) (v : Vector α n) (rest : Matrix α m n) : Matrix α (m + 1) n

/--
info: @[reducible] def Matrix.empty.noConfusion.{u_1, u} : {α : Type u} → (P : Sort u_1) → Matrix.empty = Matrix.empty → P → P
-/
#guard_msgs in #print sig Matrix.empty.noConfusion

/--
info: @[reducible] def Matrix.row.noConfusion.{u_1, u} : {α : Type u} →
  (P : Sort u_1) →
    (n m : Nat) →
      (v : Vector α n) →
        (rest : Matrix α m n) →
          (v' : Vector α n) →
            (rest' : Matrix α m n) → Matrix.row n m v rest = Matrix.row n m v' rest' → (v = v' → rest = rest' → P) → P
-/
#guard_msgs in #print sig Matrix.row.noConfusion

-- Test 3: Mutual inductive types
mutual
  inductive Tree (α : Type u) : Type u where
    | leaf (val : α) : Tree α
    | node (forest : Forest α) : Tree α

  inductive Forest (α : Type u) : Type u where
    | empty : Forest α
    | cons (tree : Tree α) (rest : Forest α) : Forest α
end

-- Verify noConfusion for mutual inductives
/--
info: @[reducible] def Tree.leaf.noConfusion.{u_1, u} : {α : Type u} →
  (P : Sort u_1) → (val val' : α) → Tree.leaf val = Tree.leaf val' → (val = val' → P) → P
-/
#guard_msgs in #print sig Tree.leaf.noConfusion
/--
info: @[reducible] def Tree.node.noConfusion.{u_1, u} : {α : Type u} →
  (P : Sort u_1) → (forest forest' : Forest α) → Tree.node forest = Tree.node forest' → (forest = forest' → P) → P
-/
#guard_msgs in #print sig Tree.node.noConfusion
/--
info: @[reducible] def Forest.empty.noConfusion.{u_1, u} : {α : Type u} → (P : Sort u_1) → Forest.empty = Forest.empty → P → P
-/
#guard_msgs in #print sig Forest.empty.noConfusion
/--
info: @[reducible] def Forest.cons.noConfusion.{u_1, u} : {α : Type u} →
  (P : Sort u_1) →
    (tree : Tree α) →
      (rest : Forest α) →
        (tree' : Tree α) →
          (rest' : Forest α) → Forest.cons tree rest = Forest.cons tree' rest' → (tree = tree' → rest = rest' → P) → P
-/
#guard_msgs in #print sig Forest.cons.noConfusion

-- Test 4: Higher-order inductive with function types
inductive HigherOrder (α : Type) : Type 1 where
  | base (x : α) : HigherOrder α
  | func (f : α → HigherOrder α) : HigherOrder α

-- Test noConfusion with function arguments
/--
info: @[reducible] def HigherOrder.base.noConfusion.{u} : {α : Type} →
  (P : Sort u) → (x x' : α) → HigherOrder.base x = HigherOrder.base x' → (x = x' → P) → P
-/
#guard_msgs in #print sig HigherOrder.base.noConfusion
/--
info: @[reducible] def HigherOrder.func.noConfusion.{u} : {α : Type} →
  (P : Sort u) → (f f' : α → HigherOrder α) → HigherOrder.func f = HigherOrder.func f' → (f = f' → P) → P
-/
#guard_msgs in #print sig HigherOrder.func.noConfusion

-- Test 5: Nested inductive with complex dependency
inductive Nested : Type 1 where
  | simple (n : Nat) : Nested
  | complex (inner : List Nested) : Nested

-- Test recursive nesting in noConfusion
/--
info: @[reducible] def Nested.simple.noConfusion.{u} : (P : Sort u) →
  (n n' : Nat) → Nested.simple n = Nested.simple n' → (n = n' → P) → P
-/
#guard_msgs in #print sig Nested.simple.noConfusion
/--
info: @[reducible] def Nested.complex.noConfusion.{u} : (P : Sort u) →
  (inner inner' : List Nested) → Nested.complex inner = Nested.complex inner' → (inner = inner' → P) → P
-/
#guard_msgs in #print sig Nested.complex.noConfusion

-- Test 6: Inductive with universe polymorphism
inductive UnivPoly.{u, v} (α : Type u) (β : Type v) : Type (max u v) where
  | left (a : α) : UnivPoly α β
  | right (b : β) : UnivPoly α β
  | both (a : α) (b : β) : UnivPoly α β

-- Test universe-polymorphic noConfusion
/--
info: @[reducible] def UnivPoly.left.noConfusion.{u_1, u, v} : {α : Type u} →
  {β : Type v} → (P : Sort u_1) → (a a' : α) → UnivPoly.left a = UnivPoly.left a' → (a = a' → P) → P
-/
#guard_msgs in #print sig UnivPoly.left.noConfusion
/--
info: @[reducible] def UnivPoly.right.noConfusion.{u_1, u, v} : {α : Type u} →
  {β : Type v} → (P : Sort u_1) → (b b' : β) → UnivPoly.right b = UnivPoly.right b' → (b = b' → P) → P
-/
#guard_msgs in #print sig UnivPoly.right.noConfusion
/--
info: @[reducible] def UnivPoly.both.noConfusion.{u_1, u, v} : {α : Type u} →
  {β : Type v} →
    (P : Sort u_1) →
      (a : α) → (b : β) → (a' : α) → (b' : β) → UnivPoly.both a b = UnivPoly.both a' b' → (a = a' → b = b' → P) → P
-/
#guard_msgs in #print sig UnivPoly.both.noConfusion

-- Test 7: Inductive with implicit arguments and type classes
inductive WithTypeClass (α : Type u) [Inhabited α] : Type u where
  | default : WithTypeClass α
  | custom (val : α) : WithTypeClass α

-- Test noConfusion with type class constraints
/--
info: @[reducible] def WithTypeClass.default.noConfusion.{u_1, u} : {α : Type u} →
  [inst : Inhabited α] → (P : Sort u_1) → WithTypeClass.default = WithTypeClass.default → P → P
-/
#guard_msgs in #print sig WithTypeClass.default.noConfusion
/--
info: @[reducible] def WithTypeClass.custom.noConfusion.{u_1, u} : {α : Type u} →
  [inst : Inhabited α] →
    (P : Sort u_1) → (val val' : α) → WithTypeClass.custom val = WithTypeClass.custom val' → (val = val' → P) → P
-/
#guard_msgs in #print sig WithTypeClass.custom.noConfusion

-- Test 8: Very complex indexed family with dependent types
inductive ComplexVec (α : Type u) : (n : Nat) → (valid : n > 0) → Type u where
  | single (x : α) : ComplexVec α 1 (by simp)
  | extend {n : Nat} {h : n > 0} (x : α) (rest : ComplexVec α n h) :
    ComplexVec α (n + 1) (by simp)

/--
info: @[reducible] def ComplexVec.extend.noConfusion.{u_1, u} : {α : Type u} →
  (P : Sort u_1) →
    {n : Nat} →
      {h : n > 0} →
        (x : α) →
          (rest : ComplexVec α n h) →
            (h' : n > 0) →
              (x' : α) →
                (rest' : ComplexVec α n h') →
                  ComplexVec.extend x rest = ComplexVec.extend x' rest' → (x = x' → rest = rest' → P) → P
-/
#guard_msgs in #print sig ComplexVec.extend.noConfusion

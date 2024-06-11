import Lean

open Lean Meta

def genHCongr (declName : Name) : MetaM Unit := do
  let info ← getConstInfo declName
  let thm ← mkHCongr (mkConst declName <| info.levelParams.map Level.param)
  IO.println (← ppExpr thm.type)

def genCongr (declName : Name) : MetaM Unit := do
  let info ← getConstInfo declName
  let some thm ← mkCongrSimp? (mkConst declName <| info.levelParams.map Level.param) | return ()
  IO.println (← ppExpr thm.type)

/--
info: ∀ (coll coll' : Type u),
  coll = coll' →
    ∀ (idx idx' : Type v),
      idx = idx' →
        ∀ (elem elem' : Type w),
          elem = elem' →
            ∀ (valid : coll → idx → Prop) (valid' : coll' → idx' → Prop),
              HEq valid valid' →
                ∀ (self : GetElem coll idx elem valid) (self' : GetElem coll' idx' elem' valid'),
                  HEq self self' →
                    ∀ (xs : coll) (xs' : coll'),
                      HEq xs xs' →
                        ∀ (i : idx) (i' : idx'),
                          HEq i i' → ∀ (h : valid xs i) (h' : valid' xs' i'), HEq h h' → HEq xs[i] xs'[i']
-/
#guard_msgs in
#eval genHCongr ``GetElem.getElem

/--
info: ∀ {coll : Type u} {idx : Type v} {elem : Type w} {valid : coll → idx → Prop} [self : GetElem coll idx elem valid]
  (xs xs_1 : coll) (e_xs : xs = xs_1) (i i_1 : idx) (e_i : i = i_1) (h : valid xs i), xs[i] = xs_1[i_1]
-/
#guard_msgs in
#eval genCongr ``GetElem.getElem

def f (x := 0) (_ : x = x := by rfl) := x + 1

/--
info: ∀ (x x' : Nat), x = x' → ∀ (x_1 : x = x) (x'_1 : x' = x'), HEq x_1 x'_1 → HEq (f x x_1) (f x' x'_1)
-/
#guard_msgs in
#eval genHCongr ``f

/-- info: ∀ (x x_1 : Nat) (e_x : x = x_1) (x_2 : x = x), f x x_2 = f x_1 ⋯ -/
#guard_msgs in
#eval genCongr ``f

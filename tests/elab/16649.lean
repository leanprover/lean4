/-
Kernel: `is_def_eq_unit_like` downcasts an arbitrary constant to `constructor_val` and reads
`get_nfields()` out of it. It does this while `add_inductive` checks a mutual block, before the
block's constructor names are checked.

Run:  lean Repro.lean        (tested on Lean v4.37.0-rc1)

In `type_checker::is_def_eq_unit_like` (src/kernel/type_checker.cpp):

    name ctor_name = head(env().get(const_name(I)).to_inductive_val().get_cnstrs());
    constructor_val ctor_val = env().get(ctor_name).to_constructor_val();   // unchecked downcast
    if (ctor_val.get_nfields() != 0) return false;

`add_inductive` declares all types of a mutual block first (`declare_inductive_types`), then
checks the constructors type by type (`check_constructors` calls `check_name` on a constructor
only when it reaches it), and declares the constructors last. So while `I1.mk` is checked, `I2`
is in the environment with a constructor list naming ANY existing constant.

The block (no constructor field mentions the block, so `I2` is a non-recursive structure):

    I1 : Nat → Type
    I1.mk : I1 ((fun (_ : (P : I2 → Prop) → (x y : I2) → P x → P y) => 0) (fun P x y h => h))
    I2 : Type,   one constructor  c2 : I2

The argument has type `... → P x → P x`, so the application is well typed only if `x ≡ y` for
two distinct variables `x y : I2`. The last rule the kernel tries is `is_def_eq_unit_like`.

How to read the output:
  * "application type mismatch": the unit-like rule declined (`x ≢ y`), so `I1.mk` is rejected.
  * "invalid return type for 'I1.mk'": the unit-like rule FIRED (`x ≡ y` was accepted), so the
    application passed. The kernel then rejected the block for an unrelated reason: `I1.mk`'s
    index mentions `I2`.

Expected: the rule depends on `I2`'s OWN constructor (it has none yet, so it should decline or
throw). Actual: it depends on what `c2` happens to name. For an inductive (`Empty`, `False`) or a
definition (`id`, `Nat.add`), `get_nfields()` reads a field of a record with another layout.
For `ConstantInfo.inductInfo` the 5th object field is `ctors`, which is `[]` (boxed 0) for
`Empty`. `DefinitionVal` has only 4 object fields, so the read lands in its scalar area.
-/
import Lean
open Lean Meta

/-- Each case uses its own namespace `ns`: a failed `addDecl` can leave the block's types in
    the elaborator's environment, so the names must not be reused. -/
def mkBlock (ns c2 : Name) : Declaration :=
  let I1 := ns ++ `I1
  let I2 := ns ++ `I2
  let i2 := mkConst I2
  let pTy := mkForall `_ .default i2 (mkSort Level.zero)
  -- (P : I2 → Prop) → (x y : I2) → P x → P y    (P = #2, x = #1, y = #0 under three binders)
  let fty := mkForall `P .default pTy (mkForall `x .default i2 (mkForall `y .default i2
               (mkForall `h .default (mkApp (mkBVar 2) (mkBVar 1)) (mkApp (mkBVar 3) (mkBVar 1)))))
  let fn := mkLambda `_ .default fty (mkConst ``Nat.zero)
  -- fun P x y (h : P x) => h        : (P : I2 → Prop) → (x y : I2) → P x → P x
  let arg := mkLambda `P .default pTy (mkLambda `x .default i2 (mkLambda `y .default i2
               (mkLambda `h .default (mkApp (mkBVar 2) (mkBVar 1)) (mkBVar 0))))
  let mk1 := mkApp (mkConst I1) (mkApp fn arg)
  .inductDecl [] 0 [{ name := I1, type := mkForall `n .default (mkConst ``Nat) (mkSort Level.one),
                      ctors := [{ name := I1 ++ `mk, type := mk1 }] },
                    { name := I2, type := mkSort Level.one, ctors := [{ name := c2, type := i2 }] }] false

def tryBlock (label : String) (ns c2 : Name) : MetaM Unit := do
  try addDecl (mkBlock ns c2); IO.println s!"{label}: accepted"
  catch e => IO.println s!"{label}: {(← e.toMessageData.toString).splitOn "\n" |>.head!}"

-- the normal case: a fresh name
/-- info: c2 = I2.c         (fresh name)            : (kernel) application type mismatch -/
#guard_msgs in
#eval tryBlock "c2 = I2.c         (fresh name)            " `case1 `case1.I2.c
-- c2 names a constructor of ANOTHER type
/-- info: c2 = Nat.succ     (ctor of Nat, 1 field)  : (kernel) application type mismatch -/
#guard_msgs in
#eval tryBlock "c2 = Nat.succ     (ctor of Nat, 1 field)  " `case2 ``Nat.succ
/-- info: c2 = PUnit.unit   (ctor of PUnit, 0 fields): (kernel) application type mismatch -/
#guard_msgs in
#eval tryBlock "c2 = PUnit.unit   (ctor of PUnit, 0 fields)" `case3 ``PUnit.unit
-- c2 names a constant that is NOT a constructor: the downcast reads a record of another layout
/-- info: c2 = Empty        (an inductive type)     : (kernel) application type mismatch -/
#guard_msgs in
#eval tryBlock "c2 = Empty        (an inductive type)     " `case4 ``Empty
/-- info: c2 = False        (an inductive type)     : (kernel) application type mismatch -/
#guard_msgs in
#eval tryBlock "c2 = False        (an inductive type)     " `case5 ``False
/-- info: c2 = id           (a definition)          : (kernel) application type mismatch -/
#guard_msgs in
#eval tryBlock "c2 = id           (a definition)          " `case6 ``id
/-- info: c2 = Nat.add      (a definition)          : (kernel) application type mismatch -/
#guard_msgs in
#eval tryBlock "c2 = Nat.add      (a definition)          " `case7 ``Nat.add
/-- info: c2 = propext      (an axiom)              : (kernel) application type mismatch -/
#guard_msgs in
#eval tryBlock "c2 = propext      (an axiom)              " `case8 ``propext

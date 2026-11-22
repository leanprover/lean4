/-
Kernel: `infer_proj` types a projection from whatever constant the structure's constructor list
names, even when that constant is not a constructor of the structure (or not a constructor at
all).

Run:  lean Repro.lean        (tested on Lean v4.37.0-rc1)

In `type_checker::infer_proj` (src/kernel/type_checker.cpp):

    constant_info c_info = env().get(head(I_val.get_cnstrs()));     // no is_constructor() check
    expr r = instantiate_type_lparams(c_info, const_levels(I));

`add_inductive` declares all types of a mutual block first (`declare_inductive_types`), then
checks the constructors type by type (`check_constructors` calls `check_name` on a constructor
only when it reaches it), and declares the constructors last. So while `I1.mk` is checked, `I2`
is in the environment with a constructor list naming ANY existing constant.

The block:

    I1 : Type,   I1.mk : (x : I2) → Fin (Nat.succ x.1) → I1
    I2 : Type,   one constructor  c2 : Nat → I2

How to read the output:
  * "unknown constant 'I2.c'" / "invalid projection": `infer_proj` failed on `x.1`.
  * "constant has already been declared '<c2>'": `I1.mk` PASSED its check, so `x.1` was typed
    `Nat` from `c2`'s type. The block was then rejected only by the later name check on `I2`'s
    constructor.

Expected: `x.1` cannot be typed (`I2` has no constructor yet), as in the fresh-name case.
Actual: it is typed from a constructor of `Nat`, from a definition (`Nat.pred`), from an
inductive type (`Fin : Nat → Type`), or from a theorem (`Nat.succ_le_succ : ∀ {n m : Nat}, ...`).
-/
import Lean
open Lean Meta

/-- Each case uses its own namespace `ns`: a failed `addDecl` can leave the block's types in
    the elaborator's environment, so the names must not be reused. -/
def mkBlock (ns c2 : Name) : Declaration :=
  let I1 := ns ++ `I1
  let I2 := ns ++ `I2
  let i2 := mkConst I2
  let ty := mkSort Level.one
  let mk1 := mkForall `x .default i2
              (mkForall `f .default (mkApp (mkConst ``Fin) (mkApp (mkConst ``Nat.succ) (mkProj I2 0 (mkBVar 0)))) (mkConst I1))
  let mk2 := mkForall `n .default (mkConst ``Nat) i2
  .inductDecl [] 0 [{ name := I1, type := ty, ctors := [{ name := I1 ++ `mk, type := mk1 }] },
                    { name := I2, type := ty, ctors := [{ name := c2, type := mk2 }] }] false

def tryBlock (label : String) (ns c2 : Name) : MetaM Unit := do
  try addDecl (mkBlock ns c2); IO.println s!"{label}: accepted"
  catch e => IO.println s!"{label}: {(← e.toMessageData.toString).splitOn "\n" |>.head!}"

-- normal case: a fresh constructor name; `infer_proj` cannot find it
/-- info: c2 = I2.c              (fresh name)           : (kernel) invalid projection -/
#guard_msgs in
#eval tryBlock "c2 = I2.c              (fresh name)           " `case1 `case1.I2.c
-- `Nat.zero : Nat` is not a Pi, so `infer_proj` fails with "invalid projection"
/-- info: c2 = Nat.zero          (ctor of Nat, not a Pi): (kernel) invalid projection -/
#guard_msgs in
#eval tryBlock "c2 = Nat.zero          (ctor of Nat, not a Pi)" `case2 ``Nat.zero
-- in each of these, `x.1 : Nat` is read off the type of an unrelated constant and I1.mk passes
/-- info: c2 = Nat.succ          (ctor of Nat)          : (kernel) invalid projection -/
#guard_msgs in
#eval tryBlock "c2 = Nat.succ          (ctor of Nat)          " `case3 ``Nat.succ
/-- info: c2 = Nat.pred          (a definition)         : (kernel) invalid projection -/
#guard_msgs in
#eval tryBlock "c2 = Nat.pred          (a definition)         " `case4 ``Nat.pred
/-- info: c2 = Fin               (an inductive type)    : (kernel) invalid projection -/
#guard_msgs in
#eval tryBlock "c2 = Fin               (an inductive type)    " `case5 ``Fin
/-- info: c2 = Nat.succ_le_succ  (a theorem)            : (kernel) invalid projection -/
#guard_msgs in
#eval tryBlock "c2 = Nat.succ_le_succ  (a theorem)            " `case6 ``Nat.succ_le_succ

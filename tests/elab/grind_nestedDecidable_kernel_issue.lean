module
public meta import Lean.Elab.Command
/-!
Paul Reichert's examples: `grind` + kernel interaction through `Grind.nestedDecidable`.

`grind` canonicalizes `Decidable` instances under the identity wrapper `Grind.nestedDecidable`,
leaving the kernel to check `X =?= nestedDecidable p X'`, where `X'` is `X` with normalized
arguments. With a `regular` reducibility hint on the wrapper, the kernel's lazy delta reduction
unfolds `X` first, and reducing it below runs into `Nat.add` on a free variable and `4294967264`.
`Grind.nestedDecidable` is an `abbrev`, so the kernel unfolds the wrapper first.

`MyChar` mirrors `Char.toUpper` and `Char.isLower`, so that `Char` simprocs do not affect the
example.

An earlier version of this test (using `Char.isLower`) used `&&` (and `decide`) instead of `if`, but
since then, `Decidable` has become a subtype of `Bool`, and when using `decide`, Lean only compares
the `Bool` field and ignores the attached proof.
However, the issue is still reproducible with `if` because the kernel compares the instance of an
`ite` directly. The expensive part is comparing the `Decidable.reflects_decide` proofs' types,
where WHNF unfolds `Reflects` and ends up with a matcher whose discriminant is the `Bool` field.
Lean then continues WHNF'ing the `Bool` field, which is very expensive.
So comparisons of `if`'s end up WHNF'ing the `Decidable` instance's boolean value, while comparisons
of `decide` simply *compare* the boolean values without WHNF'ing.

While it is good that `nestedDecidable` is now marked as highly reducible to the kernel,
it would still be worthwhile to investigate two things.
(a) Can we avoid the full WHNF when comparing `if`'s, or more generally, when comparing
    `Decidable` instances?
(b) Why is WHNF'ing `UInt32` arithmetic so terribly inefficient? Can we at least stop it from
    exploding?
-/

section Test

set_option maxHeartbeats 1000 -- for the health of the machine

structure MyChar where
  val : UInt32

def MyChar.toUpper (c : MyChar) : MyChar :=
  if 97 ≤ c.val ∧ c.val ≤ 122 then ⟨c.val + (65 - 97)⟩ else c

def MyChar.isLower (c : MyChar) : Bool :=
  if 97 ≤ c.val ∧ c.val ≤ 122 then true else false

/-!
After `split`, the instance of the `if` from `isLower` is `instDecidableAnd (UInt32.decLe 97 {val := c.val + (65 - 97)}.val) ..`.
`grind` normalizes the condition to `97 ≤ c.val + 4294967264 ∧ ..` and wraps the instance with the
projection reduced, so the kernel has to check the two instances against each other.
-/
theorem MyChar.isLower_toUpper (c : MyChar) : c.toUpper.isLower = false := by
  unfold MyChar.isLower MyChar.toUpper
  split <;> grind only

end Test

section Control

/-!
Sanity check: The test above used to fail if `nestedDecidable` is just a reducible definition,
lacking the `abbrev` kernel hint that it has on the current toolchain. Now that the kernel cancels
`Nat` offsets in one step, it passes either way.
-/

/-- `Grind.nestedDecidable` with a `regular` reducibility hint. -/
@[reducible]
def regularNestedDecidable {p : Prop} (h : Decidable p) : Decidable p := h

open Lean Elab Command in
/--
Re-checks the proofs of `thm` and its auxiliary lemmas that mention `Grind.nestedDecidable`, with
that constant replaced by `regularNestedDecidable`.
-/
elab "#recheck_with_regular_wrapper " thm:ident : command => liftCoreM do
  let thm ← realizeGlobalConstNoOverload thm
  let some v := (← getConstInfo thm).value? (allowOpaque := true) | throwError "no value"
  let mentionsWrapper (e : Expr) := (e.find? (·.isConstOf ``Grind.nestedDecidable)).isSome
  let replace (e : Expr) := e.replace fun e =>
    if e.isConstOf ``Grind.nestedDecidable then some (mkConst ``regularNestedDecidable) else none
  let mut found := false
  for n in #[thm] ++ v.getUsedConstants.filter (thm.isPrefixOf ·) do
    let ci ← getConstInfo n
    let some v := ci.value? (allowOpaque := true) | continue
    unless mentionsWrapper v do continue
    found := true
    addDecl <| .thmDecl { name := n ++ `regular, levelParams := ci.levelParams, type := replace ci.type, value := replace v }
  unless found do throwError "neither `{thm}` nor its auxiliary lemmas mention `Grind.nestedDecidable`"

set_option maxHeartbeats 1000

#guard_msgs in
#recheck_with_regular_wrapper MyChar.isLower_toUpper

end Control

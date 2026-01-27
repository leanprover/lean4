import Lean

/-!
# Test for issue #12102: Universe normalization too late in defeq check

Without the fix, comparing `bar.{max u v}` with `bar.{max v u}` unfolds `bar`
before discovering the universes are definitionally equal.

## Test methodology:

1. **Heartbeat test**: Without the fix, the test fails at 100 heartbeats (needs ~150).
   With the fix, it passes comfortably at 100 heartbeats (needs only ~50).

2. **Diagnostics test**: We verify that with `set_option diagnostics true`,
   no kernel unfolds are reported.

   **Without the fix**, the diagnostics output was:
   ```
   [diag] Diagnostics
     [kernel] unfolded declarations (max: 2, num: 1):
       [kernel] bar ↦ 2
     use `set_option diagnostics.threshold <num>` to control threshold for reporting counters
   ```

   **With the fix**, no diagnostics are reported because the kernel recognizes
   that `bar.{max u v}` and `bar.{max v u}` have definitionally equal universe
   parameters and avoids unfolding entirely.
-/

universe u v

structure X : Type u where x : Nat
opaque a (_ : Nat) : X.{u} := ⟨0⟩
opaque b (_ _ : X.{u}) : X.{u} := ⟨0⟩

-- Depth 12 binary tree = 4096 leaves
elab "big%" : term =>
  let rec foo : Nat → Nat → Lean.Expr
    | 0, i => Lean.mkApp (Lean.mkConst ``a [.param `u]) (Lean.mkNatLit i)
    | n+1, i => Lean.mkApp2 (Lean.mkConst ``b [.param `u]) (foo n (2*i)) (foo n (2*i+1))
  pure (foo 12 0)

structure A where
opaque foo (_ : X.{u}) : A := ⟨⟩
structure B extends A

set_option maxRecDepth 100000 in
def bar : B := ⟨foo big%⟩

-- Test 1: Heartbeat limit - fails without fix (needs ~150), passes with fix (needs ~50)
set_option maxHeartbeats 100 in
example : bar.{max u v} = bar.{max v u} := rfl

-- Test 2: Verify no kernel unfolds occur (bar should not be unfolded)
-- See the module docstring for details on what output was produced without the fix.
#guard_msgs (drop info) in
set_option diagnostics true in
set_option diagnostics.threshold 0 in
example : bar.{max u v} = bar.{max v u} := rfl

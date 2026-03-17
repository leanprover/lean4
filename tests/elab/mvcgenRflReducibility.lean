import Std.Tactic.Do

/-!
This test case from Hax asserts that `mspec` doesn't use default reducibility when trying
`SPred.entails.rfl`. If it did, then the `MyShl.shl a 32` would be unfolded deeply and we'd run
into timeouts.
-/

open Std.Do

set_option mvcgen.warning false

abbrev RustM := Except String

class MyAdd (Self : Type) (Rhs : Type)
  where
  add : (Self -> Rhs -> RustM Self)

instance : MyAdd UInt64 UInt64 := {
  add x y := if BitVec.uaddOverflow x.toBitVec y.toBitVec then Except.error "" else pure (x + y)
}

class MyShl (Self : Type) (Rhs : Type)
  where
  shl : (Self -> Rhs -> RustM Self)

instance : MyShl UInt64 Int32 := {
  shl x y := pure (x <<< (UInt64.ofNat y.toInt.toNat))
}

-- Cannot close the proof with `sorry` due to heartbeat limit, so we'll just capture the error message.
/--
error: unsolved goals
case vc1
a : UInt64
⊢ (wp⟦MyShl.shl a 32⟧
      (fun a =>
        wp⟦do
            let a ← MyAdd.add 0 a
            pure a⟧
          (PostCond.noThrow fun r => ⌜True⌝),
        ExceptConds.false)).down
-/
#guard_msgs in
example (a : UInt64) :
    ⦃⌜True⌝⦄
      do
        let a ← MyShl.shl a (32: Int32)
        let a ← MyAdd.add (0 : UInt64) a
        pure a
    ⦃PostCond.noThrow fun r => ⌜True⌝⦄ := by
  mvcgen -trivial -- (deterministic) timeout at `whnf`, maximum number of heartbeats (200000) has been reached

/-!
Regression test for #13921.

The executable code of a recursive definition comes from its `_unsafe_rec` implementation. When that
implementation cannot be compiled (e.g. its body is noncomputable), the user-facing definition is
left without executable code; inside a `noncomputable section` this is tolerated and only the
`_unsafe_rec` auxiliary is marked `noncomputable`. The code generator's computability check must
therefore also consult the `_unsafe_rec` name, otherwise such a definition is treated as computable.
Previously, using it as an instance field crashed the code generator with a panic in `ExplicitBoxing`
instead of reporting a clean error (or being accepted when everything is noncomputable).
-/

-- Well-founded recursion with a noncomputable body, used as an instance field. This used to panic
-- the code generator. Since everything here is in a `noncomputable section`, it is accepted.
noncomputable section
set_option warn.sorry false in
def fWF (n : Nat) : Nat := fWF (Classical.choice ⟨n⟩)
termination_by n
decreasing_by sorry

instance : Neg Nat where neg := fWF
end

-- Structural recursion with a noncomputable body.
noncomputable section
def fStruct : Nat → Nat
  | 0 => Classical.choice ⟨0⟩
  | n+1 => fStruct n
end

-- Using such a definition in a computable context reports a clean error rather than panicking.
/--
error: failed to compile definition, consider marking it as 'noncomputable' because it depends on 'fWF', which is 'noncomputable'
-/
#guard_msgs in
def useWF (n : Nat) : Nat := fWF n

/--
error: failed to compile definition, consider marking it as 'noncomputable' because it depends on 'fStruct', which is 'noncomputable'
-/
#guard_msgs in
def useStruct (n : Nat) : Nat := fStruct n

-- Normal computable recursive definitions are unaffected.
def goodWF (n : Nat) : Nat := if n = 0 then 0 else goodWF (n - 1)
termination_by n

def goodStruct : Nat → Nat
  | 0 => 0
  | n+1 => goodStruct n + 1

/-- info: 0 -/
#guard_msgs in
#eval goodWF 5

/-- info: 5 -/
#guard_msgs in
#eval goodStruct 5

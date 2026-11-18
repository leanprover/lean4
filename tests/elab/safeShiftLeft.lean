/-!
Left shifts of literals whose shift amount is above the `shiftLeft.threshold` option are not
evaluated by `whnf` and `simp`. `cbv` and the compiler use the default value of the option as a
constant bound. The runtime implementation of `Nat.shiftLeft` aborts the process when the shift
amount does not fit in 32 bits (#15193).
-/

-- `whnf`

/--
warning: shift amount 4294967296 exceeds the threshold 65536, left shift operation was not evaluated, use `set_option shiftLeft.threshold <num>` to set a new threshold
---
error: maximum recursion depth has been reached
use `set_option maxRecDepth <num>` to increase limit
use `set_option diagnostics true` to get diagnostic information
-/
#guard_msgs in
example : (1 <<< 4294967296 : Nat) = 0 := by rfl

/--
warning: shift amount 4294967296 exceeds the threshold 65536, left shift operation was not evaluated, use `set_option shiftLeft.threshold <num>` to set a new threshold
---
error: maximum recursion depth has been reached
use `set_option maxRecDepth <num>` to increase limit
use `set_option diagnostics true` to get diagnostic information
-/
#guard_msgs in
example : (1 <<< 4294967296 : Nat) = 0 := by decide

#guard_msgs in
example : (1 <<< 100 : Nat) = 1267650600228229401496703205376 := by rfl

#guard_msgs in
example : (1 <<< 65536 : Nat) % 2 = 0 := by rfl

/--
warning: shift amount 9 exceeds the threshold 8, left shift operation was not evaluated, use `set_option shiftLeft.threshold <num>` to set a new threshold
-/
#guard_msgs in
set_option shiftLeft.threshold 8 in
example : (1 <<< 9 : Nat) = 512 := by rfl

#guard_msgs in
set_option shiftLeft.threshold 100000 in
example : (1 <<< 65537 : Nat) % 2 = 0 := by rfl

#guard_msgs in
example : (0 <<< 4294967296 : Nat) = 0 := by rfl

-- `simp`

/--
warning: shift amount 4294967296 exceeds the threshold 65536, left shift operation was not evaluated, use `set_option shiftLeft.threshold <num>` to set a new threshold
---
error: unsolved goals
⊢ False
-/
#guard_msgs in
example : (1 <<< 4294967296 : Nat) = 0 := by simp

/--
error: unsolved goals
⊢ False
-/
#guard_msgs in
example : (1 <<< 4294967296 : Nat) = 0 := by simp -warnExponents

/--
warning: shift amount 65537 exceeds the threshold 65536, left shift operation was not evaluated, use `set_option shiftLeft.threshold <num>` to set a new threshold
---
error: `simp` made no progress
-/
#guard_msgs in
example (x : Nat) : (1 <<< 65537 : Nat) = x := by simp

/--
warning: shift amount 4294967296 exceeds the threshold 65536, left shift operation was not evaluated, use `set_option shiftLeft.threshold <num>` to set a new threshold
---
error: `simp` made no progress
-/
#guard_msgs in
example (x : Fin 5000000000) : ((3 : Fin 5000000000) <<< (4294967296 : Fin 5000000000)) = x := by simp

/--
warning: shift amount 4294967296 exceeds the threshold 65536, left shift operation was not evaluated, use `set_option shiftLeft.threshold <num>` to set a new threshold
---
error: unsolved goals
x : BitVec (8 + 4294967296)
⊢ (1#8).shiftLeftZeroExtend 4294967296 = x
-/
#guard_msgs in
example (x : BitVec (8 + 4294967296)) : BitVec.shiftLeftZeroExtend 1#8 4294967296 = x := by simp

#guard_msgs in
example : (1#8 <<< (4294967296 : Nat)) = 0#8 := by simp

#guard_msgs in
example : (1#8 <<< 4294967296#64) = 0#8 := by simp

#guard_msgs in
example : BitVec.shiftLeft 1#8 4294967296 = 0#8 := by simp

/--
warning: shift amount 70000 exceeds the threshold 65536, left shift operation was not evaluated, use `set_option shiftLeft.threshold <num>` to set a new threshold
---
error: `simp` made no progress
-/
#guard_msgs in
example (x : BitVec 100000) : (1#100000 <<< (70000 : Nat)) = x := by simp only [BitVec.reduceHShiftLeft]

/--
warning: shift amount 70000 exceeds the threshold 65536, left shift operation was not evaluated, use `set_option shiftLeft.threshold <num>` to set a new threshold
---
error: `simp` made no progress
-/
#guard_msgs in
example (x : BitVec 100000) : BitVec.shiftLeft 1#100000 70000 = x := by simp only [BitVec.reduceShiftLeft]

#guard_msgs in
example : (1 <<< 100 : Nat) = 1267650600228229401496703205376 := by simp

#guard_msgs in
example : (1 <<< 65536 : Nat) % 2 = 0 := by simp

#guard_msgs in
example : (1#8 <<< (3 : Nat)) = 8#8 := by simp

#guard_msgs in
example : (1#8 <<< 3#8) = 8#8 := by simp

#guard_msgs in
example : BitVec.shiftLeft 1#8 3 = 8#8 := by simp

#guard_msgs in
example : BitVec.shiftLeftZeroExtend 1#8 3 = 8#11 := by simp

#guard_msgs in
example : ((3 : Fin 10) <<< (1 : Fin 10)) = 6 := by simp

#guard_msgs in
set_option shiftLeft.threshold 100000 in
example : (1 <<< 65537 : Nat) % 2 = 0 := by simp

/--
warning: shift amount 9 exceeds the threshold 8, left shift operation was not evaluated, use `set_option shiftLeft.threshold <num>` to set a new threshold
---
error: `simp` made no progress
-/
#guard_msgs in
set_option shiftLeft.threshold 8 in
example (x : Nat) : (1 <<< 9 : Nat) = x := by simp

#guard_msgs in
example : (0 <<< 4294967296 : Nat) = 0 := by simp only [Nat.reduceShiftLeft]

#guard_msgs in
example : (0#8 <<< (4294967296 : Nat)) = 0#8 := by simp only [BitVec.reduceHShiftLeft]

#guard_msgs in
example : BitVec.shiftLeft 0#8 4294967296 = 0#8 := by simp only [BitVec.reduceShiftLeft]

#guard_msgs in
example : ((0 : Fin 5000000000) <<< (4294967296 : Fin 5000000000)) = 0 := by simp only [Fin.reduceShiftLeft]

/--
warning: shift amount 4294967296 does not fit in 32 bits, left shift operation was not evaluated
---
error: `simp` made no progress
-/
#guard_msgs in
set_option shiftLeft.threshold 5000000000 in
example (x : Nat) : (1 <<< 4294967296 : Nat) = x := by simp

/--
warning: shift amount 4294967296 does not fit in 32 bits, left shift operation was not evaluated
---
error: `simp` made no progress
-/
#guard_msgs in
set_option shiftLeft.threshold 5000000000 in
example (x : BitVec 8) : (1#8 <<< (4294967296 : Nat)) = x := by simp only [BitVec.reduceHShiftLeft]

-- `cbv`

/--
error: maximum recursion depth has been reached
use `set_option maxRecDepth <num>` to increase limit
use `set_option diagnostics true` to get diagnostic information
-/
#guard_msgs in
example : (1 <<< 4294967296 : Nat) = 0 := by cbv

/--
error: maximum recursion depth has been reached
use `set_option maxRecDepth <num>` to increase limit
use `set_option diagnostics true` to get diagnostic information
-/
#guard_msgs in
example : ((1 : Int) <<< (4294967296 : Nat)) = 0 := by cbv

/--
error: maximum recursion depth has been reached
use `set_option maxRecDepth <num>` to increase limit
use `set_option diagnostics true` to get diagnostic information
-/
#guard_msgs in
example : (1#8 <<< (4294967296 : Nat)) = 0#8 := by cbv

/--
error: maximum recursion depth has been reached
use `set_option maxRecDepth <num>` to increase limit
use `set_option diagnostics true` to get diagnostic information
-/
#guard_msgs in
example : (1#8 <<< 4294967296#64) = 0#8 := by cbv

/--
error: maximum recursion depth has been reached
use `set_option maxRecDepth <num>` to increase limit
use `set_option diagnostics true` to get diagnostic information
-/
#guard_msgs in
example : ((3 : Fin 5000000000) <<< (4294967296 : Fin 5000000000)) = 0 := by cbv

/--
error: maximum recursion depth has been reached
use `set_option maxRecDepth <num>` to increase limit
use `set_option diagnostics true` to get diagnostic information
-/
#guard_msgs in
example : BitVec.shiftLeft 1#8 4294967296 = 0#8 := by cbv

/--
error: maximum recursion depth has been reached
use `set_option maxRecDepth <num>` to increase limit
use `set_option diagnostics true` to get diagnostic information
-/
#guard_msgs in
example (x : BitVec (8 + 4294967296)) : BitVec.shiftLeftZeroExtend 1#8 4294967296 = x := by cbv

#guard_msgs in
example : (1 <<< 100 : Nat) = 1267650600228229401496703205376 := by cbv

#guard_msgs in
example : (1 <<< 65536 : Nat) % 2 = 0 := by cbv

#guard_msgs in
example : ((1 : Int) <<< (3 : Nat)) = 8 := by cbv

#guard_msgs in
example : (1#8 <<< (3 : Nat)) = 8#8 := by cbv

#guard_msgs in
example : (1#8 <<< 3#8) = 8#8 := by cbv

#guard_msgs in
example : BitVec.shiftLeft 1#8 3 = 8#8 := by cbv

#guard_msgs in
example : BitVec.shiftLeftZeroExtend 1#8 3 = 8#11 := by cbv

#guard_msgs in
example : ((3 : Fin 10) <<< (1 : Fin 10)) = 6 := by cbv

#guard_msgs in
example : ((1 : UInt64) <<< (4294967296 : UInt64)) = 1 := by cbv

-- `cbv` uses its own bound (`maxShiftLeft`), and does not read the `shiftLeft.threshold` option.
/--
error: maximum recursion depth has been reached
use `set_option maxRecDepth <num>` to increase limit
use `set_option diagnostics true` to get diagnostic information
-/
#guard_msgs in
set_option shiftLeft.threshold 100000 in
example : (1 <<< 65537 : Nat) % 2 = 0 := by cbv

#guard_msgs in
example : (0 <<< 4294967296 : Nat) = 0 := by cbv

#guard_msgs in
example : ((0 : Int) <<< (4294967296 : Nat)) = 0 := by cbv

#guard_msgs in
example : (0#8 <<< (4294967296 : Nat)) = 0#8 := by cbv

#guard_msgs in
example : (0#8 <<< 4294967296#64) = 0#8 := by cbv

#guard_msgs in
example : BitVec.shiftLeft 0#8 4294967296 = 0#8 := by cbv

#guard_msgs in
example : ((0 : Fin 5000000000) <<< (4294967296 : Fin 5000000000)) = 0 := by cbv

-- Compiler: the constant folder evaluates shift amounts below 65536 only.

#guard_msgs in
def shiftHuge : Nat := 1 <<< 4294967296

#guard_msgs in
def shiftZero : Nat := 0 <<< 4294967296

/--
trace: [Compiler.result] size: 3
    def shiftNoFold._closed_0 : tobj :=
      let _x.1 := 65536;
      let _x.2 := 1;
      let _x.3 := Nat.shiftLeft _x.2 _x.1;
      return _x.3
[Compiler.result] size: 2
    def shiftNoFold @&x : tobj :=
      let _x.1 := shiftNoFold._closed_0;
      let _x.2 := Nat.add x _x.1;
      return _x.2
[Compiler.result] size: 2
    def shiftNoFold._boxed x : tobj :=
      let res := shiftNoFold x;
      dec x;
      return res
-/
#guard_msgs in
set_option trace.Compiler.result true in
def shiftNoFold (x : Nat) : Nat := x + (1 <<< 65536)

/--
trace: [Compiler.result] size: 2
    def shiftFold @&x : tobj :=
      let _x.1 := 256;
      let _x.2 := Nat.add x _x.1;
      return _x.2
[Compiler.result] size: 2
    def shiftFold._boxed x : tobj :=
      let res := shiftFold x;
      dec x;
      return res
-/
#guard_msgs in
set_option trace.Compiler.result true in
def shiftFold (x : Nat) : Nat := x + (1 <<< 8)

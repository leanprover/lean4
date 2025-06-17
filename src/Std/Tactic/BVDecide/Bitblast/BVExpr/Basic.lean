/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
prelude
import Init.Data.Hashable
import Init.Data.BitVec.Lemmas
import Init.Data.RArray
import Std.Tactic.BVDecide.Bitblast.BoolExpr.Basic

/-!
This module contains the definition of the `BitVec` fragment that `bv_decide` internally operates
on as `BVLogicalExpr`. The preprocessing steps of `bv_decide` reduce all supported `BitVec`
operations to the ones provided in this file. For verification purposes `BVLogicalExpr.Sat` and
`BVLogicalExpr.Unsat` are provided.
-/

namespace Std.Tactic.BVDecide

/--
The variable definition used by the bitblaster.
-/
structure BVBit where
  /--
  A numeric identifier for the BitVec variable.
  -/
  var : Nat
  /--
  The width of the BitVec variable.
  -/
  {w : Nat}
  /--
  The bit that we take out of the BitVec variable by getLsb.
  -/
  idx : Fin w
  deriving Hashable, DecidableEq, Repr

instance : ToString BVBit where
  toString b := s!"x{b.var}[{b.idx.val}]"

instance : Inhabited BVBit where
  default := { w := 1, var := 0, idx := 0 }

/--
All supported binary operations on `BVExpr`.
-/
inductive BVBinOp where
  /--
  Bitwise and.
  -/
  | and
  /--
  Bitwise or.
  -/
  | or
  /--
  Bitwise xor.
  -/
  | xor
  /--
  Addition.
  -/
  | add
  /--
  Multiplication.
  -/
  | mul
  /--
  Unsigned division.
  -/
  | udiv
  /--
  Unsigned modulo.
  -/
  | umod
  deriving Hashable, DecidableEq

namespace BVBinOp

def toString : BVBinOp → String
  | and => "&&"
  | or => "||"
  | xor => "^"
  | add => "+"
  | mul => "*"
  | udiv => "/ᵤ"
  | umod => "%ᵤ"

instance : ToString BVBinOp := ⟨toString⟩

/--
The semantics for `BVBinOp`.
-/
def eval : BVBinOp → (BitVec w → BitVec w → BitVec w)
  | and => (· &&& ·)
  | or => (· ||| ·)
  | xor => (· ^^^ ·)
  | add => (· + ·)
  | mul => (· * ·)
  | udiv => (· / ·)
  | umod => (· % · )

@[simp] theorem eval_and : eval .and = ((· &&& ·) : BitVec w → BitVec w → BitVec w) := by rfl
@[simp] theorem eval_or : eval .or = ((· ||| ·) : BitVec w → BitVec w → BitVec w) := by rfl
@[simp] theorem eval_xor : eval .xor = ((· ^^^ ·) : BitVec w → BitVec w → BitVec w) := by rfl
@[simp] theorem eval_add : eval .add = ((· + ·) : BitVec w → BitVec w → BitVec w) := by rfl
@[simp] theorem eval_mul : eval .mul = ((· * ·) : BitVec w → BitVec w → BitVec w) := by rfl
@[simp] theorem eval_udiv : eval .udiv = ((· / ·) : BitVec w → BitVec w → BitVec w) := by rfl
@[simp] theorem eval_umod : eval .umod = ((· % ·) : BitVec w → BitVec w → BitVec w) := by rfl

end BVBinOp

/--
All supported unary operators on `BVExpr`.
-/
inductive BVUnOp where
  /--
  Bitwise not.
  -/
  | not
  /--
  Rotating left by a constant value.
  -/
  | rotateLeft (n : Nat)
  /--
  Rotating right by a constant value.
  -/
  | rotateRight (n : Nat)
  /--
  Arithmetic shift right by a constant value.

  This operation has a dedicated constant representation as shiftRight can take `Nat` as a shift amount.
  We can obviously not bitblast a `Nat` but still want to support the case where the user shifts by a
  constant `Nat` value.
  -/
  | arithShiftRightConst (n : Nat)
  /--
  Reverse the bits in a bitvector.
  -/
  | reverse
  deriving Hashable, DecidableEq

namespace BVUnOp

def toString : BVUnOp → String
  | not => "~"
  | rotateLeft n => s!"rotL {n}"
  | rotateRight n => s!"rotR {n}"
  | arithShiftRightConst n => s!">>a {n}"
  | reverse => "rev"

instance : ToString BVUnOp := ⟨toString⟩

/--
The semantics for `BVUnOp`.
-/
def eval : BVUnOp → (BitVec w → BitVec w)
  | not => (~~~ ·)
  | rotateLeft n => (BitVec.rotateLeft · n)
  | rotateRight n => (BitVec.rotateRight · n)
  | arithShiftRightConst n => (BitVec.sshiftRight · n)
  | reverse =>  BitVec.reverse

@[simp] theorem eval_not : eval .not = ((~~~ ·) : BitVec w → BitVec w) := by rfl

@[simp]
theorem eval_rotateLeft : eval (rotateLeft n) = ((BitVec.rotateLeft · n) : BitVec w → BitVec w) := by
  rfl

@[simp]
theorem eval_rotateRight : eval (rotateRight n) = ((BitVec.rotateRight · n) : BitVec w → BitVec w) := by
  rfl

@[simp]
theorem eval_arithShiftRightConst : eval (arithShiftRightConst n) = (BitVec.sshiftRight · n : BitVec w → BitVec w) := by
  rfl

@[simp] theorem eval_reverse : eval .reverse = (BitVec.reverse : BitVec w → BitVec w) := by rfl

end BVUnOp

/--
All supported expressions involving `BitVec` and operations on them.
-/
inductive BVExpr : Nat → Type where
  /--
  A `BitVec` variable, referred to through an index.
  -/
  | var (idx : Nat) : BVExpr w
  /--
  A constant `BitVec` value.
  -/
  | const (val : BitVec w) : BVExpr w
  /--
  Extract a slice from a `BitVec`.
  -/
  | extract (start len : Nat) (expr : BVExpr w) : BVExpr len
  /--
  A binary operation on two `BVExpr`.
  -/
  | bin (lhs : BVExpr w) (op : BVBinOp) (rhs : BVExpr w) : BVExpr w
  /--
  A unary operation on two `BVExpr`.
  -/
  | un (op : BVUnOp) (operand : BVExpr w) : BVExpr w
  /--
  Concatenate two bitvectors.
  -/
  | append (lhs : BVExpr l) (rhs : BVExpr r) (h : w = l + r) : BVExpr w
  /--
  Concatenate a bitvector with itself `n` times.
  -/
  | replicate (n : Nat) (expr : BVExpr w) (h : w' = w * n) : BVExpr w'
  /--
  shift left by another BitVec expression. For constant shifts there exists a `BVUnop`.
  -/
  | shiftLeft (lhs : BVExpr m) (rhs : BVExpr n) : BVExpr m
  /--
  shift right by another BitVec expression. For constant shifts there exists a `BVUnop`.
  -/
  | shiftRight (lhs : BVExpr m) (rhs : BVExpr n) : BVExpr m
  /--
  shift right arithmetically by another BitVec expression. For constant shifts there exists a `BVUnop`.
  -/
  | arithShiftRight (lhs : BVExpr m) (rhs : BVExpr n) : BVExpr m
with
  @[computed_field]
  hashCode : (w : Nat) → BVExpr w → UInt64
    | w, .var idx => mixHash 5 <| mixHash (hash w) (hash idx)
    | w, .const val => mixHash 7 <| mixHash (hash w) (hash val)
    | w, .extract start _ expr =>
      mixHash 11 <| mixHash (hash start) <| mixHash (hash w) (hashCode _ expr)
    | w, .bin lhs op rhs =>
      mixHash 13 <| mixHash (hash w) <| mixHash (hashCode _ lhs) <| mixHash (hash op) (hashCode _ rhs)
    | w, .un op operand =>
      mixHash 17 <| mixHash (hash w) <| mixHash (hash op) (hashCode _ operand)
    | w, .append lhs rhs _ =>
      mixHash 19 <| mixHash (hash w) <| mixHash (hashCode _ lhs) (hashCode _ rhs)
    | w, .replicate n expr _ =>
      mixHash 23 <| mixHash (hash w) <| mixHash (hash n) (hashCode _ expr)
    | w, .shiftLeft lhs rhs =>
      mixHash 29 <| mixHash (hash w) <| mixHash (hashCode _ lhs) (hashCode _ rhs)
    | w, .shiftRight lhs rhs =>
      mixHash 31 <| mixHash (hash w) <| mixHash (hashCode _ lhs) (hashCode _ rhs)
    | w, .arithShiftRight lhs rhs =>
      mixHash 37 <| mixHash (hash w) <| mixHash (hashCode _ lhs) (hashCode _ rhs)


namespace BVExpr

instance : Hashable (BVExpr w) where
  hash expr := expr.hashCode _

instance decEq : DecidableEq (BVExpr w) := fun l r =>
  withPtrEqDecEq l r fun _ =>
    if h : hash l ≠ hash r then
      .isFalse (ne_of_apply_ne hash h)
    else
      match l with
      | .var lidx =>
        match r with
        | .var ridx =>
          if h : lidx = ridx then .isTrue (by simp [h]) else .isFalse (by simp [h])
        | .const .. | .extract .. | .bin .. | .un .. | .append .. | .replicate .. | .shiftLeft ..
        | .shiftRight .. | .arithShiftRight .. => .isFalse (by simp)
      | .const lval =>
        match r with
        | .const rval =>
          if h : lval = rval then .isTrue (by simp [h]) else .isFalse (by simp [h])
        | .var .. | .extract .. | .bin .. | .un .. | .append .. | .replicate .. | .shiftLeft ..
        | .shiftRight .. | .arithShiftRight .. => .isFalse (by simp)
      | .extract (w := lw) lstart _ lexpr =>
        match r with
        | .extract (w := rw) rstart _ rexpr  =>
          if h1 : lw = rw ∧ lstart = rstart then
            match decEq (h1.left ▸ lexpr) rexpr with
            | .isTrue h2 => .isTrue (by cases h1.left; simp_all)
            | .isFalse h2 => .isFalse (by cases h1.left; simp_all)
          else
            .isFalse (by simp_all)
        | .var .. | .const .. | .bin .. | .un .. | .append .. | .replicate .. | .shiftLeft ..
        | .shiftRight .. | .arithShiftRight .. => .isFalse (by simp)
      | .bin llhs lop lrhs =>
        match r with
        | .bin rlhs rop rrhs =>
          if h1 : lop = rop then
            match decEq llhs rlhs, decEq lrhs rrhs with
            | .isTrue h2, .isTrue h3 => .isTrue (by simp [h1, h2, h3])
            | .isFalse h2, _ => .isFalse (by simp [h2])
            | _, .isFalse h3 => .isFalse (by simp [h3])
          else
            .isFalse (by simp [h1])
        | .const .. | .var .. | .extract .. | .un .. | .append .. | .replicate .. | .shiftLeft ..
        | .shiftRight .. | .arithShiftRight .. => .isFalse (by simp)
      | .un lop lexpr =>
        match r with
        | .un rop rexpr =>
          if h1 : lop = rop then
            match decEq lexpr rexpr with
            | .isTrue h2 => .isTrue (by simp [h1, h2])
            | .isFalse h2 => .isFalse (by simp [h2])
          else
            .isFalse (by simp [h1])
        | .const .. | .var .. | .extract .. | .bin .. | .append .. | .replicate .. | .shiftLeft ..
        | .shiftRight .. | .arithShiftRight .. => .isFalse (by simp)
      | .append (l := ll) (r := lr) llhs lrhs lh =>
        match r with
        | .append (l := rl) (r := rr) rlhs rrhs rh =>
          if h1 : ll = rl ∧ lr = rr then
            match decEq (h1.left ▸ llhs) rlhs, decEq (h1.right ▸ lrhs) rrhs with
            | .isTrue h2, .isTrue h3 => .isTrue (by cases h1.left; cases h1.right; simp [h2, h3])
            | .isFalse h2, _ => .isFalse (by cases h1.left; cases h1.right; simp [h2])
            | _, .isFalse h3 => .isFalse (by cases h1.left; cases h1.right; simp [h3])
          else
            .isFalse (by simp; omega)
        | .const .. | .var .. | .extract .. | .bin .. | .un .. | .replicate .. | .shiftLeft ..
        | .shiftRight .. | .arithShiftRight .. => .isFalse (by simp)
      | .replicate (w := lw) ln lexpr lh =>
        match r with
        | .replicate (w := rw) rn rexpr rh =>
          if h1 : ln = rn ∧ lw = rw then
            match decEq (h1.right ▸ lexpr) rexpr with
            | .isTrue h2 => .isTrue (by cases h1.left; cases h1.right; simp [h2])
            | .isFalse h2 => .isFalse (by cases h1.left; cases h1.right; simp [h2])
          else
            .isFalse (by simp; omega)
        | .const .. | .var .. | .extract .. | .bin .. | .un .. | .append .. | .shiftLeft ..
        | .shiftRight .. | .arithShiftRight .. => .isFalse (by simp)

      | .shiftLeft (n := lw) llhs lrhs =>
        match r with
        | .shiftLeft (n := rw) rlhs rrhs =>
          if h1 : lw = rw then
            match decEq llhs rlhs, decEq (h1 ▸ lrhs) rrhs with
            | .isTrue h2, .isTrue h3 => .isTrue (by cases h1; simp [h2, h3])
            | .isFalse h2, _ => .isFalse (by cases h1; simp [h2])
            | _, .isFalse h3 => .isFalse (by cases h1; simp [h3])
          else
            .isFalse (by simp [h1])
        | .const .. | .var .. | .extract .. | .bin .. | .un .. | .append .. | .replicate ..
        | .shiftRight .. | .arithShiftRight .. => .isFalse (by simp)
      | .shiftRight (n := lw) llhs lrhs =>
        match r with
        | .shiftRight (n := rw) rlhs rrhs =>
          if h1 : lw = rw then
            match decEq llhs rlhs, decEq (h1 ▸ lrhs) rrhs with
            | .isTrue h2, .isTrue h3 => .isTrue (by cases h1; simp [h2, h3])
            | .isFalse h2, _ => .isFalse (by cases h1; simp [h2])
            | _, .isFalse h3 => .isFalse (by cases h1; simp [h3])
          else
            .isFalse (by simp [h1])
        | .const .. | .var .. | .extract .. | .bin .. | .un .. | .append .. | .replicate ..
        |.shiftLeft .. | .arithShiftRight .. => .isFalse (by simp)
      | .arithShiftRight (n := lw) llhs lrhs =>
        match r with
        | .arithShiftRight (n := rw) rlhs rrhs =>
          if h1 : lw = rw then
            match decEq llhs rlhs, decEq (h1 ▸ lrhs) rrhs with
            | .isTrue h2, .isTrue h3 => .isTrue (by cases h1; simp [h2, h3])
            | .isFalse h2, _ => .isFalse (by cases h1; simp [h2])
            | _, .isFalse h3 => .isFalse (by cases h1; simp [h3])
          else
            .isFalse (by simp [h1])
        | .const .. | .var .. | .extract .. | .bin .. | .un .. | .append .. | .replicate ..
        | .shiftRight .. | .shiftLeft .. => .isFalse (by simp)

def toString : BVExpr w → String
  | .var idx => s!"var{idx}"
  | .const val => ToString.toString val
  | .extract start len expr => s!"{expr.toString}[{start}, {len}]"
  | .bin lhs op rhs => s!"({lhs.toString} {op.toString} {rhs.toString})"
  | .un op operand => s!"({op.toString} {toString operand})"
  | .append lhs rhs _ => s!"({toString lhs} ++ {toString rhs})"
  | .replicate n expr _ => s!"(replicate {n} {toString expr})"
  | .shiftLeft lhs rhs => s!"({lhs.toString} << {rhs.toString})"
  | .shiftRight lhs rhs => s!"({lhs.toString} >> {rhs.toString})"
  | .arithShiftRight lhs rhs => s!"({lhs.toString} >>a {rhs.toString})"


instance : ToString (BVExpr w) := ⟨toString⟩

/--
Pack a `BitVec` with its width into a single parameter-less structure.
-/
structure PackedBitVec where
  {w : Nat}
  bv: BitVec w

/--
The notion of variable assignments for `BVExpr`.
-/
abbrev Assignment := Lean.RArray PackedBitVec

/--
Get the value of a `BVExpr.var` from an `Assignment`.
-/
def Assignment.get (assign : Assignment) (idx : Nat) : PackedBitVec :=
  Lean.RArray.get assign idx

/--
The semantics for `BVExpr`.
-/
def eval (assign : Assignment) : BVExpr w → BitVec w
  | .var idx =>
    let packedBv := assign.get idx
    /-
    This formulation improves performance, as in a well formed expression the condition always holds
    so there is no need for the more involved `BitVec.truncate` logic.
    -/
    if h : packedBv.w = w then
      h ▸ packedBv.bv
    else
      packedBv.bv.truncate w
  | .const val => val
  | .extract start len expr => BitVec.extractLsb' start len (eval assign expr)
  | .bin lhs op rhs => op.eval (eval assign lhs) (eval assign rhs)
  | .un op operand => op.eval (eval assign operand)
  | .append lhs rhs h => h ▸ ((eval assign lhs) ++ (eval assign rhs))
  | .replicate n expr h => h ▸ (BitVec.replicate n (eval assign expr))
  | .shiftLeft lhs rhs => (eval assign lhs) <<< (eval assign rhs)
  | .shiftRight lhs rhs => (eval assign lhs) >>> (eval assign rhs)
  | .arithShiftRight lhs rhs => BitVec.sshiftRight' (eval assign lhs) (eval assign rhs)

@[simp]
theorem eval_var : eval assign ((.var idx) : BVExpr w) = (assign.get idx).bv.truncate w := by
  rw [eval]
  split
  · next h =>
    subst h
    simp
  · rfl

@[simp]
theorem eval_const : eval assign (.const val) = val := by rfl

@[simp]
theorem eval_extract : eval assign (.extract start len expr) = BitVec.extractLsb' start len (eval assign expr) := by
  rfl

@[simp]
theorem eval_bin : eval assign (.bin lhs op rhs) = op.eval (lhs.eval assign) (rhs.eval assign) := by
  rfl

@[simp]
theorem eval_un : eval assign (.un op operand) = op.eval (operand.eval assign) := by
  rfl

@[simp]
theorem eval_append : eval assign (.append lhs rhs h) = (lhs.eval assign) ++ (rhs.eval assign) := by
  rfl

@[simp]
theorem eval_replicate : eval assign (.replicate n expr h) = BitVec.replicate n (expr.eval assign) := by
  rfl

@[simp]
theorem eval_shiftLeft : eval assign (.shiftLeft lhs rhs) = (eval assign lhs) <<< (eval assign rhs) := by
  rfl

@[simp]
theorem eval_shiftRight : eval assign (.shiftRight lhs rhs) = (eval assign lhs) >>> (eval assign rhs) := by
  rfl

@[simp]
theorem eval_arithShiftRight :
    eval assign (.arithShiftRight lhs rhs) = BitVec.sshiftRight' (eval assign lhs) (eval assign rhs) := by
  rfl

end BVExpr

/--
Supported binary predicates on `BVExpr`.
-/
inductive BVBinPred where
  /--
  Equality.
  -/
  | eq
  /--
  Unsigned Less Than
  -/
  | ult

namespace BVBinPred

def toString : BVBinPred → String
  | eq => "=="
  | ult => "<u"

instance : ToString BVBinPred := ⟨toString⟩

/--
The semantics for `BVBinPred`.
-/
def eval : BVBinPred → (BitVec w → BitVec w → Bool)
  | .eq => (· == ·)
  | .ult => BitVec.ult

@[simp] theorem eval_eq : eval .eq = ((· == ·) : BitVec w → BitVec w → Bool) := by rfl
@[simp] theorem eval_ult : eval .ult = (BitVec.ult : BitVec w → BitVec w → Bool) := by rfl

end BVBinPred

/--
Supported predicates on `BVExpr`.
-/
inductive BVPred where
  /--
  A binary predicate on `BVExpr`.
  -/
  | bin (lhs : BVExpr w) (op : BVBinPred) (rhs : BVExpr w)
  /--
  Getting a constant LSB from a `BitVec`.
  -/
  | getLsbD (expr : BVExpr w) (idx : Nat)

namespace BVPred

/--
Pack two `BVExpr` of equivalent width into one parameter-less structure.
-/
structure ExprPair where
  {w : Nat}
  lhs : BVExpr w
  rhs : BVExpr w

def toString : BVPred → String
  | bin lhs op rhs => s!"({lhs.toString} {op.toString} {rhs.toString})"
  | getLsbD expr idx => s!"{expr.toString}[{idx}]"

instance : ToString BVPred := ⟨toString⟩

/--
The semantics for `BVPred`.
-/
def eval (assign : BVExpr.Assignment) : BVPred → Bool
  | bin lhs op rhs => op.eval (lhs.eval assign) (rhs.eval assign)
  | getLsbD expr idx => (expr.eval assign).getLsbD idx

@[simp]
theorem eval_bin : eval assign (.bin lhs op rhs) = op.eval (lhs.eval assign) (rhs.eval assign) := by
  rfl

@[simp]
theorem eval_getLsbD : eval assign (.getLsbD expr idx) = (expr.eval assign).getLsbD idx := by
  rfl

end BVPred

/--
Boolean substructure of problems involving predicates on BitVec as atoms.
-/
abbrev BVLogicalExpr := BoolExpr BVPred

namespace BVLogicalExpr

/--
The semantics of boolean problems involving BitVec predicates as atoms.
-/
def eval (assign : BVExpr.Assignment) (expr : BVLogicalExpr) : Bool :=
  BoolExpr.eval (·.eval assign) expr

@[simp] theorem eval_literal : eval assign (.literal pred) = pred.eval assign := rfl
@[simp] theorem eval_const : eval assign (.const b) = b := rfl
@[simp] theorem eval_not : eval assign (.not x) = !eval assign x := rfl
@[simp] theorem eval_gate : eval assign (.gate g x y) = g.eval (eval assign x) (eval assign y) := rfl
@[simp] theorem eval_ite :
  eval assign (.ite d l r) = bif (eval assign d) then (eval assign l) else (eval assign r) := rfl

def Sat (x : BVLogicalExpr) (assign : BVExpr.Assignment) : Prop := eval assign x = true

def Unsat (x : BVLogicalExpr) : Prop := ∀ f, eval f x = false

theorem sat_and {x y : BVLogicalExpr} {assign} (hx : Sat x assign) (hy : Sat y assign) :
    Sat (.gate .and x y) assign := by
  simp only [Sat] at *
  simp [hx, hy, Gate.eval]

theorem sat_true : Sat (.const true) assign := rfl

end BVLogicalExpr

end Std.Tactic.BVDecide

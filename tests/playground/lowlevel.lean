import Lean.Meta
import Lean.Compiler.IR
open Lean

inductive LowLevelType where
| Integer (bits : Nat)
| Function (args : Array LowLevelType) (ret : LowLevelType)
| Pointer (target : LowLevelType)
| Struct (name : String) (fields : Array (String × LowLevelType))
| Alias (name : String) (type : LowLevelType)

open LowLevelType

inductive LowLevelExpr : LowLevelType → Type where
| Const (bits : Nat) (value : Fin (2 ^ bits)) : LowLevelExpr (Integer bits)

open LowLevelExpr

def ByteValue := LowLevelExpr (Integer 8)
def BoolValue := LowLevelExpr (Integer 1)

def ppBool : BoolValue → String 
| Const _ ⟨1, _⟩ => "true"
| Const _ ⟨0, _⟩ => "false"

instance : ToString BoolValue := ⟨ppBool⟩

def mkByte (n : Nat) : ByteValue := LowLevelExpr.Const 8 (Fin.ofNat n)
def mkBool : Bool → BoolValue
| true => LowLevelExpr.Const 1 ⟨1, rfl⟩
| false => LowLevelExpr.Const 1 ⟨0, rfl⟩


def LeanArray := mkByte 246
def LeanStructArray := mkByte 247
def LeanScalarArray := mkByte 248
def LeanString := mkByte 249

class HasBEq (α : LowLevelType) where
  beq : LowLevelExpr α → LowLevelExpr α → BoolValue 

infix:50 " == " => HasBEq.beq

def compareInt {bits : Nat} : LowLevelExpr (Integer bits) → LowLevelExpr (Integer bits) → BoolValue
| Const _ x, Const _ y => mkBool $ x == y

instance {bits : Nat} : HasBEq (Integer bits) := ⟨compareInt⟩

class HasOr where
  or : BoolValue → BoolValue → BoolValue

infixl:30 " || " => HasOr.or

def orBool : BoolValue → BoolValue → BoolValue
| Const _ ⟨0, _⟩, Const _ ⟨0, _⟩ => mkBool false
| _, _ => mkBool true

instance : HasOr := ⟨orBool⟩


def lean_is_big_object_tag (tag : ByteValue) :=
  tag == LeanArray || tag == LeanStructArray || tag == LeanScalarArray || tag == LeanString

def test : MetaM Unit := 
  let expr := lean_is_big_object_tag (mkByte 247)
  IO.println s!"{expr}"


#eval Lean.IR.emitLLVM
#eval test
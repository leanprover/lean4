/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/
module

prelude

public import Lean.Data.Json
public import Lean.Kernel.InLean.Basic
public import Lean.Kernel.InLean.ExprOps

/-!
# InLean: the Nat-operation pin variants

InLean does not import ConLeche, so it embeds the **same dumps**
con-leche splices (one JSON file per toolchain, `ConLeche.Kernel.NatOpPins`,
in the same order) with `include_str`, and decodes their share tables
(`ConLeche.PinGen.Dump`'s encoding) into `Lean.Expr` one operation at a
time: when a pin-certified operation is declared, its entry in a variant is
found by name (`PinScan.opText`) and only that entry is parsed, decoded and
range-checked (`PinSet.op?`).  Nothing is decoded at process start or for
any other declaration, and nothing is memoised: each of the eight names is
declared once per environment.  Binder names are anonymous: the pins are
compared by definitional equality.  Nothing here is generated from the
compiling toolchain.
-/

@[expose] public section

namespace Lean.Kernel.InLean

open Lean

/-- One operation's pin data in one variant. -/
structure PinOp where
  op : Name
  pin : Expr
  proofs : Array Expr
  typePins : Array (Name × Expr)
  deriving Inhabited

/-- Every term of one operation's pin data is in range (`EO.inRange`). -/
def PinOp.inRange (op : PinOp) : Bool :=
  EO.inRange op.pin && op.proofs.all EO.inRange && op.typePins.all (EO.inRange ·.2)

namespace PinDecode

/-- A decoded share-table entry. -/
inductive Obj where
  | name (n : Name)
  | level (l : Level)
  | expr (e : Expr)
  deriving Inhabited

def getRef (tab : Array Obj) (j : Json) : Except String Obj :=
  match j with
  | .str "anon" => pure (.name .anonymous)
  | .str "lzero" => pure (.level .zero)
  | _ => do
    let i ← j.getNat?
    match tab[i]? with
    | some o => pure o
    | none => throw s!"pin reference {i} out of range"

def refName (tab : Array Obj) (j : Json) : Except String Name := do
  match ← getRef tab j with
  | .name n => pure n
  | _ => throw "pin reference: expected a name"

def refLevel (tab : Array Obj) (j : Json) : Except String Level := do
  match ← getRef tab j with
  | .level l => pure l
  | _ => throw "pin reference: expected a level"

def refExpr (tab : Array Obj) (j : Json) : Except String Expr := do
  match ← getRef tab j with
  | .expr e => pure e
  | _ => throw "pin reference: expected an expression"

def entry (tab : Array Obj) (j : Json) : Except String Obj := do
  let a ← j.getArr?
  let at? (i : Nat) : Except String Json :=
    match a[i]? with
    | some v => pure v
    | none => throw s!"pin entry field {i} missing"
  let tag ← (← at? 0).getStr?
  match tag with
  | "ns" => return .name (.str (← refName tab (← at? 1)) (← (← at? 2).getStr?))
  | "nn" => return .name (.num (← refName tab (← at? 1)) (← (← at? 2).getNat?))
  | "ls" => return .level (.succ (← refLevel tab (← at? 1)))
  | "lM" => return .level (.max (← refLevel tab (← at? 1)) (← refLevel tab (← at? 2)))
  | "lI" => return .level (.imax (← refLevel tab (← at? 1)) (← refLevel tab (← at? 2)))
  | "lp" => return .level (.param (← refName tab (← at? 1)))
  | "b" => return .expr (mkBvar (← (← at? 1).getNat?))
  | "s" => return .expr (.sort (← refLevel tab (← at? 1)))
  | "c" =>
    let us ← (← at? 2).getArr?
    return .expr (.const (← refName tab (← at? 1)) (← us.toList.mapM (refLevel tab)))
  | "a" => return .expr (.app (← refExpr tab (← at? 1)) (← refExpr tab (← at? 2)))
  | "lam" => return .expr (.lam .anonymous (← refExpr tab (← at? 1)) (← refExpr tab (← at? 2)) .default)
  | "fa" => return .expr (.forallE .anonymous (← refExpr tab (← at? 1)) (← refExpr tab (← at? 2)) .default)
  | "le" => return .expr (.letE .anonymous (← refExpr tab (← at? 1)) (← refExpr tab (← at? 2))
      (← refExpr tab (← at? 3)) false)
  | "ln" => return .expr (.lit (.natVal (← (← at? 1).getNat?)))
  | "lstr" => return .expr (.lit (.strVal (← (← at? 1).getStr?)))
  | "p" => return .expr (.proj (← refName tab (← at? 1)) (← (← at? 2).getNat?) (← refExpr tab (← at? 3)))
  | t => throw s!"pin entry tag {t} not supported here"

def blob (j : Json) : Except String Expr := do
  let es ← (← j.getObjVal? "entries").getArr?
  let mut tab : Array Obj := #[]
  for e in es do
    tab := tab.push (← entry tab e)
  refExpr tab (← j.getObjVal? "root")

def opDump (j : Json) : Except String PinOp := do
  let op := (← (← j.getObjVal? "op").getStr?).toName
  let pin ← blob (← j.getObjVal? "pin")
  let proofs ← (← (← j.getObjVal? "proofs").getArr?).mapM blob
  let typePins ← (← (← j.getObjVal? "typePins").getArr?).mapM fun t => do
    pure ((← (← t.getObjVal? "name").getStr?).toName, ← blob (← t.getObjVal? "type"))
  return { op, pin, proofs, typePins }

end PinDecode

/-! ## Finding one operation in a dump

A dump is one JSON object; its `ops` member, the last, is an array of one
object per operation, whose first member `op` names it.  Only the operation
being declared is decoded: `PinScan` finds its object by a byte search for
the key (`"op":"<name>"`, after the `"ops":` key) and its end by bracket
depth (strings skipped), and `Json.parse` reads that span alone.  In valid
JSON the six bytes `"op":"` only occur as a key `op` with a string value
(an unescaped quote neither occurs in a string nor follows one).  The search
reads no value: a span it gets wrong fails to parse or to decode, or decodes
to terms the checks refuse, so it is not part of what the checker trusts. -/

namespace PinScan

/-- Do the bytes of `key` from its index `j` on occur in `b` at `i + j`? -/
def matchAt (b key : ByteArray) (i j : Nat) : Bool :=
  if h : j < key.size then b[i + j]?.getD 0 == key[j] && matchAt b key i (j + 1) else true
termination_by key.size - j

/-- The first index from `i` at which `key` (starting with a quote) occurs. -/
def findKey (b key : ByteArray) (i : Nat) : Option Nat :=
  if h : i < b.size then
    if b[i] == 34 && matchAt b key i 1 then some i else findKey b key (i + 1)
  else none
termination_by b.size - i

/-- The index of the first quote from `i` (the end of a string with no
escape, as names are). -/
def quoteAt (b : ByteArray) (i : Nat) : Nat :=
  if h : i < b.size then (if b[i] == 34 then i else quoteAt b (i + 1)) else b.size
termination_by b.size - i

/-- The index after the bracket closing depth `d` (`inStr`: inside a string). -/
def nestEnd (b : ByteArray) (i d : Nat) (inStr : Bool) : Nat :=
  if h : i < b.size then
    let x := b[i]
    if inStr then
      if x == 92 then nestEnd b (i + 2) d true else nestEnd b (i + 1) d (x != 34)
    else if x == 34 then nestEnd b (i + 1) d true
    else if x == 123 || x == 91 then nestEnd b (i + 1) (d + 1) false
    else if x == 125 || x == 93 then (if d ≤ 1 then i + 1 else nestEnd b (i + 1) (d - 1) false)
    else nestEnd b (i + 1) d false
  else b.size
termination_by b.size - i

/-- The last index at or before `i` that is not JSON whitespace. -/
def backWs (b : ByteArray) : Nat → Nat
  | 0 => 0
  | i + 1 =>
    let x := b[i + 1]?.getD 0
    if x == 32 || x == 10 || x == 13 || x == 9 then backWs b i else i + 1

/-- The dump's bytes `[s, e)` (`b` the dump's bytes; the indices are at
ASCII bytes, so at character boundaries). -/
def text (dump : String) (s e : Nat) : String := String.Pos.Raw.extract dump ⟨s⟩ ⟨e⟩

/-- The string value of the key occurrence at `k` (`key` its bytes up to the
value's opening quote). -/
def strValue (dump : String) (b key : ByteArray) (k : Nat) : String :=
  let v := k + key.size
  text dump v (quoteAt b v)

/-- The object of operation `c` among the `op` keys from `i` on (`f`: fuel,
the dump's size, as every round moves past one byte at least). -/
def opFrom (dump : String) (b : ByteArray) (c : Name) : Nat → Nat → Option String
  | 0, _ => none
  | f + 1, i =>
    match findKey b "\"op\":\"".toByteArray i with
    | none => none
    | some k =>
      if (strValue dump b "\"op\":\"".toByteArray k).toName == c then
        let s := backWs b (k - 1)
        if b[s]?.getD 0 == 123 then some (text dump s (nestEnd b s 0 false)) else none
      else opFrom dump b c f (k + 1)

/-- The text of operation `c`'s object in a dump, if it has one. -/
def opText (dump : String) (c : Name) : Option String :=
  let b := dump.toByteArray
  match findKey b "\"ops\":".toByteArray 0 with
  | some k => opFrom dump b c b.size (k + 1)
  | none => none

/-- A dump's `toolchain` member (for messages). -/
def toolchain (dump : String) : String :=
  let b := dump.toByteArray
  match findKey b "\"toolchain\":\"".toByteArray 0 with
  | some k => strValue dump b "\"toolchain\":\"".toByteArray k
  | none => "?"

end PinScan

/-- One pin variant (twin of `NatOpPinSet`): one committed dump, read one
operation at a time (`PinSet.op?`). -/
structure PinSet where
  dump : String
  deriving Inhabited

/-- The variant's toolchain (for messages). -/
def PinSet.toolchain (ps : PinSet) : String := PinScan.toolchain ps.dump

/-- **Operation `c`'s pin data in the variant**, decoded when `c` is
declared and only then (the variant's other operations are not read), and
in range; `none` where the variant has no pin for `c`. -/
def PinSet.op? (ps : PinSet) (c : Name) : Except String (Option PinOp) := do
  match PinScan.opText ps.dump c with
  | none => return none
  | some t =>
    let op ← PinDecode.opDump (← Json.parse t)
    unless op.inRange do throw s!"a pin term of {c} is out of range"
    return some op

/-- The variants, in con-leche's order (the dump of con-leche's toolchain
first). -/
def pinSets : Array PinSet := #[
  ⟨include_str "pins/leanprover-lean4-nightly-nightly-2026-09-10.json"⟩,
  ⟨include_str "pins/leanprover-lean4-v4.33.0.json"⟩,
  ⟨include_str "pins/leanprover-lean4-v4.34.0-rc2.json"⟩]

end Lean.Kernel.InLean

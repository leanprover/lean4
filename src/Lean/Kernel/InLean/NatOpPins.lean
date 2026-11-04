/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/
module

prelude

public import Lean.Data.Json
public import Lean.Kernel.InLean.Basic

/-!
# InLean: the Nat-operation pin variants

InLean embeds the **same dumps** con-leche splices (`pins/<toolchain>.json`, `ConLeche/Kernel/NatOpPins.lean`,
in the same order) with `include_str`, and decodes their share tables
(`ConLeche/PinGen/Dump.lean`'s encoding) into `Lean.Expr` when a
pin-certified operation is declared — eight times per run, so the decode
is not memoised.  Binder names are anonymous: the pins are compared by
definitional equality.  Nothing here is generated from the compiling
toolchain.
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

/-- One pin variant (twin of `NatOpPinSet`). -/
structure PinSet where
  toolchain : String
  ops : Array PinOp
  deriving Inhabited

def PinSet.op? (ps : PinSet) (c : Name) : Option PinOp :=
  ps.ops.find? (·.op == c)

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
  | "b" => return .expr (.bvar (← (← at? 1).getNat?))
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

def pinSet (s : String) : Except String PinSet := do
  let j ← Json.parse s
  let tc ← (← j.getObjVal? "toolchain").getStr?
  let ops ← (← (← j.getObjVal? "ops").getArr?).mapM opDump
  return { toolchain := tc, ops }

end PinDecode

/-- The committed dumps, in con-leche's order (the repository toolchain's
first). -/
def pinDumpTexts : Array String := #[
  include_str "pins/leanprover-lean4-nightly-nightly-2026-09-10.json",
  include_str "pins/leanprover-lean4-v4.33.0.json",
  include_str "pins/leanprover-lean4-v4.34.0-rc2.json"]

/-- Decode the pin variants (at use: a function, so nothing runs at
process start). -/
def loadPinSets (_ : Unit) : Except String (Array PinSet) :=
  pinDumpTexts.mapM PinDecode.pinSet

end Lean.Kernel.InLean

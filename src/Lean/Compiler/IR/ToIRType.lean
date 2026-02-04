/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.Compiler.IR.Format
public import Lean.Compiler.LCNF.MonoTypes

public section

namespace Lean
namespace IR

open Lean.Compiler

def nameToIRType (n : Name) : IRType :=
  match n with
  | ``Float => .float
  | ``Float32 => .float32
  | ``UInt8 => .uint8
  | ``UInt16 => .uint16
  | ``UInt32 => .uint32
  | ``UInt64 => .uint64
  | ``lcErased => .erased
  | `obj => .object
  | `tobj => .tobject
  | `tagged => .tagged
  | ``lcVoid => .void
  | _ => unreachable!


def toIRType (type : Lean.Expr) : IRType :=
  match type with
  | LCNF.ImpureType.float => .float
  | LCNF.ImpureType.float32 => .float32
  | LCNF.ImpureType.uint8 => .uint8
  | LCNF.ImpureType.uint16 => .uint16
  | LCNF.ImpureType.uint32 => .uint32
  | LCNF.ImpureType.uint64 => .uint64
  | LCNF.ImpureType.usize => .usize
  | LCNF.ImpureType.erased => .erased
  | LCNF.ImpureType.object => .object
  | LCNF.ImpureType.tobject => .tobject
  | LCNF.ImpureType.tagged => .tagged
  | LCNF.ImpureType.void => .void
  | _ => unreachable!

end IR
end Lean

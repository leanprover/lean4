/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Marc Huisinga
-/
module

prelude
public import Init.Data.Ord.Basic
public import Init.Data.String.Subslice
import Init.Data.Hashable
import Init.Data.ToString
public import Lean.Syntax

set_option linter.coreInternal.internalModule false

deriving instance Hashable, Ord for String.Pos.Raw
deriving instance Hashable, Ord for String.Slice.Pos
deriving instance BEq, Hashable for String.Slice.Subslice

public instance : ToString (String.Slice.Subslice s) where
  toString s := s!"{s.startInclusive.offset} - {s.endExclusive.offset}"

public instance : Repr (String.Slice.Subslice s) where
  reprPrec s _ := toString s

public def Lean.SourceInfo.getLeading? (info : SourceInfo) : Option Substring.Raw :=
  match info with
  | original (leading := leading) .. => some leading
  | _ => none

public def Lean.Syntax.getLeading? (stx : Syntax) : Option Substring.Raw :=
  stx.getHeadInfo.getLeading?

public def Lean.Syntax.getStartPos? (stx : Syntax) : Option String.Pos.Raw :=
  let info := stx.getHeadInfo
  info.getLeading?.map (·.startPos) <|> info.getPos?

public def Lean.Syntax.Range.ofSubstring (s : Substring.Raw) : Syntax.Range :=
  ⟨s.startPos, s.stopPos⟩

public instance [Monad m] : MonadLift Option (OptionT m) where
  monadLift o? := (pure o? : m (Option _))

public def Option.split (o : Option (α × β)) : Option α × Option β := (o.map (·.1), o.map (·.2))

public def Lean.Syntax.TSepArray.ofElemsAndSeps
    (elems : TSyntaxArray kinds) (seps : Array (Option Syntax)) (sep : String)
    : TSepArray kinds sep :=
  let elemsAndSeps : Array Syntax :=
    elems.zip seps
      |>.flatMap fun (elem, sep?) =>
        let sep := sep?.getD mkNullNode
        #[elem, sep]
  ⟨elemsAndSeps⟩

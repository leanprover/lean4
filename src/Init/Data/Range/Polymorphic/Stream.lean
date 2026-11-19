/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Init.Data.Range.Polymorphic.Iterators
public import Init.Data.Stream

public section

open Std.Iterators

namespace Std.PRange

instance {α} [UpwardEnumerable α] : ToStream (Rcc α) (Iter (α := Rxc.Iterator α) α) where
  toStream r := Rcc.Internal.iter r

instance {α} [UpwardEnumerable α] : ToStream (Rco α) (Iter (α := Rxo.Iterator α) α) where
  toStream r := Rco.Internal.iter r

instance {α} [UpwardEnumerable α] : ToStream (Rci α) (Iter (α := Rxi.Iterator α) α) where
  toStream r := Rci.Internal.iter r

instance {α} [UpwardEnumerable α] : ToStream (Roc α) (Iter (α := Rxc.Iterator α) α) where
  toStream r := Roc.Internal.iter r

instance {α} [UpwardEnumerable α] : ToStream (Roo α) (Iter (α := Rxo.Iterator α) α) where
  toStream r := Roo.Internal.iter r

instance {α} [UpwardEnumerable α] [Least? α] : ToStream (Roi α) (Iter (α := Rxi.Iterator α) α) where
  toStream r := Roi.Internal.iter r

instance {α} [UpwardEnumerable α] [Least? α] : ToStream (Ric α) (Iter (α := Rxc.Iterator α) α) where
  toStream r := Ric.Internal.iter r

instance {α} [UpwardEnumerable α] [Least? α] : ToStream (Rio α) (Iter (α := Rxo.Iterator α) α) where
  toStream r := Rio.Internal.iter r

instance {α} [UpwardEnumerable α] [Least? α] : ToStream (Rii α) (Iter (α := Rxi.Iterator α) α) where
  toStream r := Rii.Internal.iter r

end Std.PRange

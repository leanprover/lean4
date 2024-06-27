/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/
import Init.Data.Char.UnicodeSkipList
import Init.Data.Char.Tables

namespace Char

def isNumeric (c : Char) : Bool :=
  UnicodeSkipList.search UnicodeSkipList.numericTable c

end Char

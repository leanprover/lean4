/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.system.platform
import init.data.char.basic

namespace System
namespace FilePath
open Platform

/-- The character that separates directories. In the case where more than one character is possible, `pathSeparator` is the 'ideal' one. -/
def pathSeparator : Char :=
if isWindows then '\\' else '/'

/-- The list of all possible separators. -/
def pathSeparators : List Char :=
if isWindows then ['\\', '/'] else ['/']

/-- The character that is used to separate the entries in the $PATH environment variable. -/
def searchPathSeparator : Char :=
if isWindows then ';' else ':'

/-- File extension character -/
def extSeparator : Char :=
'.'

end FilePath
end System

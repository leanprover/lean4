/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
prelude
import Std.Time
import Std.Internal.UV.System
import Std.Data.HashMap

open Std Time

namespace Std
namespace Internal
namespace IO
namespace Async
namespace Process

/--
A group identifier, typically a numeric ID like in UNIX (e.g. 1000).
-/
structure GroupId where
  /--
  The numeric group ID.
  -/
  toNat : Nat
deriving Inhabited, DecidableEq, Ord

instance : Repr GroupId where
  reprPrec g := Repr.addAppParen ("GroupId.mk " ++ repr g.toNat)

/--
A user identifier, typically a numeric ID like in UNIX (e.g. 1001).
-/
structure UserId where
  /--
  The numeric user ID.
  -/
  toNat : Nat
deriving Inhabited, DecidableEq, Ord

instance : Repr UserId where
  reprPrec u := Repr.addAppParen ("UserId.mk " ++ repr u.toNat)

/--
A process identifier, typically a numeric ID like in UNIX (e.g. 1001).
-/
structure PId where
  /--
  The numeric process ID.
  -/
  toUInt64 : UInt64
deriving Inhabited, DecidableEq, Ord

instance : Repr PId where
  reprPrec u := Repr.addAppParen ("PId.mk " ++ repr u.toUInt64)

/--
Information about the current user.
-/
structure SystemUser where
  /--
  The user's name.
  -/
  username : String

  /--
  The user's ID.
  -/
  userId : Option UserId

  /--
  The group the user belongs to.
  -/
  groupId : Option GroupId

  /--
  The user's login shell.
  -/
  shell : Option String

  /--
  The home directory of the user.
  -/
  homeDir : Option System.FilePath
deriving Inhabited, DecidableEq, Repr

/--
Information about a group.
-/
structure GroupInfo where
  /--
  The name of the group.
  -/
  groupName : String

  /--
  The ID of the group.
  -/
  groupId : GroupId

  /--
  The list of users in the group.
  -/
  members : Array String
  deriving Repr, Inhabited

/--
Gets the title of the current process.
-/
@[inline]
def getProcessTitle : IO String :=
  UV.System.getProcessTitle

/--
Sets the title of the current process.
-/
@[inline]
def setProcessTitle (title : String) : IO Unit :=
  UV.System.setProcessTitle title

/--
Gets the current process id.
-/
@[inline]
def getId : IO PId :=
  PId.mk <$> UV.System.osGetPid

/--
Gets the current process parent id.
-/
@[inline]
def getParentId : IO PId :=
  PId.mk <$> UV.System.osGetPpid

/--
Gets the current working directory.
-/
@[inline]
def getCwd : IO System.FilePath :=
  UV.System.cwd

/--
Changes the current working directory to a new one.
-/
@[inline]
def setCwd (path : System.FilePath) : IO Unit :=
  UV.System.chdir path.toString

/--
Gets the scheduling priority of the current process.
-/
@[inline]
def getPriority (pid : PId) : IO Int64 :=
  UV.System.osGetPriority pid.toUInt64

/--
Sets the scheduling priority of the current process.
-/
@[inline]
def setPriority (pid : PId) (priority : Int64) : IO Unit :=
  UV.System.osSetPriority pid.toUInt64 priority

end Process
end Async
end IO
end Internal
end Std

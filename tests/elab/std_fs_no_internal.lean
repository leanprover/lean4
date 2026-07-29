import Std.FS

/-!
Checks that importing `Std.FS` does not re-export the raw filesystem implementation types.
-/

/--
error: Unknown identifier `Std.Internal.FS.File`
-/
#guard_msgs in
#check Std.Internal.FS.File

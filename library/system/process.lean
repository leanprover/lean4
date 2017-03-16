import init.data.list.basic

inductive process.stdio
| piped
| inherit
| null

structure process :=
(cmd : string)
/- Add an argument to pass to the process. -/
(args : list string)
/- Configuration for the process's stdin handle. -/
(stdin := stdio.inherit)
/- Configuration for the process's stdout handle. -/
(stdout := stdio.inherit)
/- Configuration for the process's stderr handle. -/
(stderr := stdio.inherit)

structure process.child (handle : Type) :=
(stdin : handle)
(stdout : handle)
(stderr : handle)

structure io.process (err : Type) (handle : Type) (m : Type → Type → Type) :=
(spawn : process → m err (process.child handle))

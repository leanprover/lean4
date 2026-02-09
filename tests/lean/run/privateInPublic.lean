module

set_option backward.privateInPublic true

private def fpriv := 1

/--
warning: Private declaration `fpriv` accessed publicly; this is allowed only because the `backward.privateInPublic` option is enabled. ⏎

Disable `backward.privateInPublic.warn` to silence this warning.
-/
#guard_msgs in
@[expose] public def fpub := fpriv

public structure S

private def S.fpriv (s : S) := s

/--
warning: Private declaration `S.fpriv` accessed publicly; this is allowed only because the `backward.privateInPublic` option is enabled. ⏎

Disable `backward.privateInPublic.warn` to silence this warning.
-/
#guard_msgs in
@[expose] public def fpub2 (s : S) := s.fpriv

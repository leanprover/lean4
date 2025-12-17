import Std.Do
import Std.Tactic.Do

open Std.Do

/-- error: `mclear` expects at an identifier -/
#guard_msgs (error) in
example : True := by mclear
/-- error: `mclear` expects at an identifier -/
#guard_msgs (error) in
example : True := by mclear
/-- error: The syntax is `mhave h := term` -/
#guard_msgs (error) in
example : True := by mhave
/-- error: The syntax is `mreplace h := term` -/
#guard_msgs (error) in
example : True := by mreplace
/-- error: `mpure` expects an identifier -/
#guard_msgs (error) in
example : True := by mpure
/-- error: `mrename_i` expects at least one identifier -/
#guard_msgs (error) in
example : True := by mrename_i
/-- error: The syntax is `mspecialize h term*` -/
#guard_msgs (error) in
example : True := by mspecialize
/-- error: The syntax is `mspecialize_pure h term*` -/
#guard_msgs (error) in
example : True := by mspecialize_pure
/-- error: The syntax is `mcases h with pat` -/
#guard_msgs (error) in
example : True := by mcases
/-- error: `mrefine` expects a pattern -/
#guard_msgs (error) in
example : True := by mrefine
/-- error: `mintro` expects at least one pattern -/
#guard_msgs (error) in
example : True := by mintro
/-- error: `mrevert` expects at least one pattern -/
#guard_msgs (error) in
example : True := by mrevert

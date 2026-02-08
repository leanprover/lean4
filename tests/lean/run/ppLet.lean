import Lean
/-!
# Some tests for pretty printing `let`/`have`-like syntax
-/

/-!
## Make sure there's no missing/additional spacing in each of the term variants.

Note: once we establish that the variants have the same basic properties, we drop down to just
testing the `let` syntax.
-/
open Lean Elab Command in
elab "#print_term " t:term : command => liftTermElabM do
  let t := t.raw.rewriteBottomUp fun s => s.unsetTrailing
  logInfo m!"{t.getKind}\n{← Lean.PrettyPrinter.ppTerm ⟨t⟩}"
/-!
### Variable, no type
-/
/--
info: Lean.Parser.Term.let
let x := 1;
x + 1
-/
#guard_msgs in #print_term let x := 1; x + 1
/--
info: Lean.Parser.Term.have
have x := 1;
x + 1
-/
#guard_msgs in #print_term have x := 1; x + 1
/--
info: Lean.Parser.Term.letI
letI x := 1;
x + 1
-/
#guard_msgs in #print_term letI x := 1; x + 1
/--
info: Lean.Parser.Term.haveI
haveI x := 1;
x + 1
-/
#guard_msgs in #print_term haveI x := 1; x + 1
/-!
### Variable, no type, with option
-/
/--
info: Lean.Parser.Term.let
let +generalize x := 1;
x + 1
-/
#guard_msgs in #print_term let +generalize x := 1; x + 1
/--
info: Lean.Parser.Term.have
have +generalize x := 1;
x + 1
-/
#guard_msgs in #print_term have +generalize x := 1; x + 1
/--
info: Lean.Parser.Term.letI
letI +generalize x := 1;
x + 1
-/
#guard_msgs in #print_term letI +generalize x := 1; x + 1
/--
info: Lean.Parser.Term.haveI
haveI +generalize x := 1;
x + 1
-/
#guard_msgs in #print_term haveI +generalize x := 1; x + 1
/-!
### No variable, no type
-/
/--
info: Lean.Parser.Term.let
let := 1;
x + 1
-/
#guard_msgs in #print_term let := 1; x + 1
/--
info: Lean.Parser.Term.have
have := 1;
x + 1
-/
#guard_msgs in #print_term have := 1; x + 1
/--
info: Lean.Parser.Term.letI
letI := 1;
x + 1
-/
#guard_msgs in #print_term letI := 1; x + 1
/--
info: Lean.Parser.Term.haveI
haveI := 1;
x + 1
-/
#guard_msgs in #print_term haveI := 1; x + 1
/-!
### No variable, no type, with option
-/
/--
info: Lean.Parser.Term.let
let +generalize := 1;
x + 1
-/
#guard_msgs in #print_term let +generalize := 1; x + 1
/--
info: Lean.Parser.Term.have
have +generalize := 1;
x + 1
-/
#guard_msgs in #print_term have +generalize := 1; x + 1
/--
info: Lean.Parser.Term.letI
letI +generalize := 1;
x + 1
-/
#guard_msgs in #print_term letI +generalize := 1; x + 1
/--
info: Lean.Parser.Term.haveI
haveI +generalize := 1;
x + 1
-/
#guard_msgs in #print_term haveI +generalize := 1; x + 1
/-!
### No variable, type
-/
/--
info: Lean.Parser.Term.let
let : Nat := 1;
x + 1
-/
#guard_msgs in #print_term let : Nat := 1; x + 1
/--
info: Lean.Parser.Term.have
have : Nat := 1;
x + 1
-/
#guard_msgs in #print_term have : Nat := 1; x + 1
/--
info: Lean.Parser.Term.letI
letI : Nat := 1;
x + 1
-/
#guard_msgs in #print_term letI : Nat := 1; x + 1
/--
info: Lean.Parser.Term.haveI
haveI : Nat := 1;
x + 1
-/
#guard_msgs in #print_term haveI : Nat := 1; x + 1
/-!
### Variable and type
-/
/--
info: Lean.Parser.Term.let
let x : Nat := 1;
x + 1
-/
#guard_msgs in #print_term let x : Nat := 1; x + 1
/--
info: Lean.Parser.Term.have
have x : Nat := 1;
x + 1
-/
#guard_msgs in #print_term have x : Nat := 1; x + 1
/--
info: Lean.Parser.Term.letI
letI x : Nat := 1;
x + 1
-/
#guard_msgs in #print_term letI x : Nat := 1; x + 1
/--
info: Lean.Parser.Term.haveI
haveI x : Nat := 1;
x + 1
-/
#guard_msgs in #print_term haveI x : Nat := 1; x + 1
/-!
### Pattern, no type
-/
/--
info: Lean.Parser.Term.let
let (rfl) := h;
foo
-/
#guard_msgs in #print_term let (rfl) := h; foo
/--
info: Lean.Parser.Term.have
have (rfl) := h;
foo
-/
#guard_msgs in #print_term have (rfl) := h; foo
/--
info: Lean.Parser.Term.letI
letI (rfl) := h;
foo
-/
#guard_msgs in #print_term letI (rfl) := h; foo
/--
info: Lean.Parser.Term.haveI
haveI (rfl) := h;
foo
-/
#guard_msgs in #print_term haveI (rfl) := h; foo
/-!
### Equations, variable, with type
-/
/--
info: Lean.Parser.Term.let
let f : Nat → Nat
  | 0 => 1
  | n + 1 => 0;
foo
-/
#guard_msgs in #print_term let f : Nat → Nat | 0 => 1 | n + 1 => 0; foo
/-!
### Equations, variable, with type, with binders
-/
/--
info: Lean.Parser.Term.let
let f (m : Nat) : Nat → Nat
  | 0 => 1
  | n + 1 => m;
foo
-/
#guard_msgs in #print_term let f (m : Nat) : Nat → Nat | 0 => 1 | n + 1 => m; foo
/-!
### Equations, no variable, with type
-/
/--
info: Lean.Parser.Term.let
let : Nat → Nat
  | 0 => 1
  | n + 1 => 0;
foo
-/
#guard_msgs in #print_term let : Nat → Nat | 0 => 1 | n + 1 => 0; foo
/-!
### Equations, no variable, with type, with binders
-/
/--
info: Lean.Parser.Term.let
let (m : Nat) : Nat → Nat
  | 0 => 1
  | n + 1 => m;
foo
-/
#guard_msgs in #print_term let (m : Nat) : Nat → Nat | 0 => 1 | n + 1 => m; foo
/-!
### Equations, no variable, no type
-/
/--
info: Lean.Parser.Term.let
let
  | 0 => 1
  | n + 1 => 0;
foo
-/
#guard_msgs in #print_term let | 0 => 1 | n + 1 => 0; foo

/-!
## `let` syntax in `do` notation
-/
/--
info: Lean.Parser.Term.do
do
  let x := 1
-/
#guard_msgs in #print_term do let x := 1
/--
info: Lean.Parser.Term.do
do
  let := 1
-/
#guard_msgs in #print_term do let := 1
/--
info: Lean.Parser.Term.do
do
  let x : Nat := 1
-/
#guard_msgs in #print_term do let x : Nat := 1
/--
info: Lean.Parser.Term.do
do
  let (rfl) := h
-/
#guard_msgs in #print_term do let (rfl) := h

/-!
## Make sure there's no missing/additional spacing in each of the tactic variants.
-/
open Lean Elab Command in
elab "#print_tactic " t:tactic : command => liftTermElabM do
  let t := t.raw.rewriteBottomUp fun s => s.unsetTrailing
  logInfo m!"{t.getKind}\n{← Lean.PrettyPrinter.ppTactic ⟨t⟩}"
/-!
The tests are similar to before
-/
/--
info: Lean.Parser.Tactic.tacticLet__
let x := 1
-/
#guard_msgs in #print_tactic let x := 1
/--
info: Lean.Parser.Tactic.tacticHave__
have x := 1
-/
#guard_msgs in #print_tactic have x := 1
/--
info: Lean.Parser.Tactic.tacticLet'__
let' x := 1
-/
#guard_msgs in #print_tactic let' x := 1
/--
info: Lean.Parser.Tactic.tacticHave'
have' x := 1
-/
#guard_msgs in #print_tactic have' x := 1
/--
info: Lean.Parser.Tactic.tacticLet'__
let' := 1
-/
#guard_msgs in #print_tactic let' := 1
/--
info: Lean.Parser.Tactic.tacticHave'
have' := 1
-/
#guard_msgs in #print_tactic have' := 1

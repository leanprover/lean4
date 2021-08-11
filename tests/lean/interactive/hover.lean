import Lean

example : True := by
  apply True.intro
      --^ textDocument/hover

example : True := by
  simp [True.intro]
      --^ textDocument/hover

example (n : Nat) : True := by
  match n with
  | Nat.zero => _
  --^ textDocument/hover
  | n + 1 => _


/-- My tactic -/
macro "mytac" o:"only"? e:term : tactic => `(exact $e)

example : True := by
  mytac only True.intro
--^ textDocument/hover
      --^ textDocument/hover
           --^ textDocument/hover

/-- My way better tactic -/
macro_rules
  | `(tactic| mytac $[only]? $e) => `(apply $e)

example : True := by
  mytac only True.intro
--^ textDocument/hover

/-- My ultimate tactic -/
elab_rules : tactic
  | `(tactic| mytac $[only]? $e) => `(tactic| refine $e) >>= Lean.Elab.Tactic.evalTactic

example : True := by
  mytac only True.intro
--^ textDocument/hover


/-- My notation -/
macro "mynota" e:term : term => e

#check mynota 1
     --^ textDocument/hover

/-- My way better notation -/
macro_rules
  | `(mynota $e) => `(2 * $e)

#check mynota 1
     --^ textDocument/hover

-- macro_rules take precedence over elab_rules for term/command, so use new syntax
syntax "mynota'" term : term

/-- My ultimate notation -/
elab_rules : term
  | `(mynota' $e) => `($e * $e) >>= (Lean.Elab.Term.elabTerm · none)

#check mynota' 1
     --^ textDocument/hover


/-- My command -/
macro "mycmd" e:term : command => `(def hi := $e)

mycmd 1
--^ textDocument/hover

/-- My way better command -/
macro_rules
  | `(mycmd $e) => `(@[inline] def hi := $e)

mycmd 1
--^ textDocument/hover

syntax "mycmd'" term : command
/-- My ultimate command -/
elab_rules : command
  | `(mycmd' $e) => `(/-- hi -/ @[inline] def hi := $e) >>= Lean.Elab.Command.elabCommand

mycmd' 1
--^ textDocument/hover


#check ({ a := })  -- should not show `sorry`
        --^ textDocument/hover

example : True := by
  simp [id True.intro]
      --^ textDocument/hover
        --^ textDocument/hover


example : Id Nat := do
  let mut n := 1
  n := 2
--^ textDocument/hover
  n

import Lean
open Lean Elab Term Meta

/-!
The kernel decides `jps% Nat n ≡ jps% N n` in time linear in `n`. The two sides differ only in
the binder type `Nat` against `N := Nat` of `n` nested join points, as the do-elaborator emits them:

```
fun x =>
  have jp : ty → ty := fun x =>
    have jp : ty → ty := fun x => … x …
    if c 1 then jp (x + 1) else jp (x + 2)
  if c 0 then jp (x + 1) else jp (x + 2)
```

`#kernel_rfl n` adds `jps% Nat n = jps% N n` with the proof `Eq.refl`, so only the kernel checks
the conversion.
-/

abbrev N := Nat

def c (i : Nat) : Bool := i % 2 == 0

syntax "jps% " term:max num : term

macro_rules
  | `(jps% $ty $n) => do
    let rec go (i k : Nat) : MacroM (TSyntax `term) := do
      match k with
      | 0 => `(x)
      | k + 1 =>
        let idx := Syntax.mkNumLit (toString i)
        let inner ← go (i + 1) k
        `(have jp : $ty → $ty := fun x => $inner
          if c $idx then jp (x + 1) else jp (x + 2))
    `(fun (x : Nat) => $(← go 0 n.getNat))

elab "#kernel_rfl " n:num : command => Command.liftTermElabM do
  let a ← instantiateMVars (← elabTermAndSynthesize (← `(jps% Nat $n)) none)
  let b ← instantiateMVars (← elabTermAndSynthesize (← `(jps% N $n)) none)
  addDecl (.thmDecl {
    name := Name.mkSimple s!"jps_rfl_{n.getNat}"
    levelParams := []
    type := ← mkEq a b
    value := ← mkEqRefl a })

set_option maxHeartbeats 1000 in
#kernel_rfl 24

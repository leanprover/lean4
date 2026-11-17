/-!
Entering `sym =>` replaces the goal by its preprocessed form, in which reducible constants such as
`N` are unfolded. The kernel must accept that replacement in time linear in the goal, also when
the unfolded constant occurs under nested `have`s.

`jps% ty n` builds `n` nested `have`s in the form of join points:

```
fun x =>
  have jp : ty → ty := fun x =>
    have jp : ty → ty := fun x => … x …
    if c 1 then jp (x + 1) else jp (x + 2)
  if c 0 then jp (x + 1) else jp (x + 2)
```

Preprocessing turns `jps% N n` into `jps% Nat n`, once in the target and once in the types of two
hypotheses.
-/

abbrev N := Nat

def c (i : Nat) : Bool := i % 2 == 0

syntax "jps% " term:max num : term

macro_rules
  | `(jps% $ty $n) => do
    let rec go (i k : Nat) : Lean.MacroM (Lean.TSyntax `term) := do
      match k with
      | 0 => `(x)
      | k + 1 =>
        let idx := Lean.Syntax.mkNumLit (toString i)
        let inner ← go (i + 1) k
        `(have jp : $ty → $ty := fun x => $inner
          if c $idx then jp (x + 1) else jp (x + 2))
    `(fun (x : Nat) => $(← go 0 n.getNat))

opaque P : (Nat → Nat) → Prop
axiom p_all (f : Nat → Nat) : P f

set_option maxHeartbeats 3000 in
example : P (jps% N 20) := by
  sym => apply p_all

opaque T : (Nat → Nat) → Type
opaque Q : Prop
axiom q_of (f : Nat → Nat) : T f → Q

set_option maxHeartbeats 3000 in
example (v : T (jps% N 20)) (w : T (jps% N 20)) : Q := by
  sym => exact q_of _ w

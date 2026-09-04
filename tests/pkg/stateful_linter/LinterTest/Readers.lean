import Lean

/-! `emitter` counts commands: its `pre` produces a `Payload` handoff (declining on terminal commands),
its `post` folds that into a persistent `Counter`. `readerA`/`readerB`/`readerC` have no `pre` pass and
no state others read (handles discarded); their `post` reads `emitter`'s pre-phase `Payload` through
its handle — exercising several post phases consuming one pre phase, handle-based cross-linter reads,
`τ ≠ σ`, declining, and the default `pre`. -/

namespace LinterTest.Readers
open Lean Elab Command

/-- Persistent (`σ`) state of `emitter`: the running command count. -/
structure Counter where
  count : Nat

/-- Pre-phase handoff (`τ`) of `emitter`: the count computed for the current command. -/
structure Payload where
  current : Nat

inductive Tree where
| node (name : String) (count : Nat) (sub : List Tree)

def Tree.getCount : Tree → Nat
  | .node _ count _ => count

def Tree.toMessageData : Tree → MessageData
  | .node name count sub =>
    let sub := m!"{name} := {count}" :: sub.map fun t => m!"• {.nest 2 t.toMessageData}"
    m!"\n".joinSep sub

instance : ToMessageData Tree := ⟨(·.toMessageData)⟩

/-- Registers a post-only linter that reports the count `emitter` staged this command, reading it
through `emitter`'s handle. Its own handoff type is irrelevant, so `τ := Unit` and the handle is
discarded (nobody reads this linter). -/
def registerReader [ToMessageData α] (emitter : StatefulLinter Counter α) (label : String) :
    IO Unit := do
  let _ ← registerStatefulLinterErgo (τ := Unit) (Counter.mk 0)
    (post := fun _ self _ => do
      if let some p := emitter.readIntermediate then
        logInfo m!"{label} sees\n{p}"
      pure self)

initialize emitter : StatefulLinter Counter Tree ←
  registerStatefulLinterErgo (Counter.mk 0)
    (pre := fun stx self =>
      pure <| if Parser.isTerminalCommand stx then none else
        let count := self.count + 1
        some <| .node "i" count [])
    (post := fun _ self preState =>
      pure { count := (preState.map (·.getCount)).getD self.count })

initialize emitter' : StatefulLinter Counter Tree ←
  registerStatefulLinterErgo (Counter.mk 0)
    (pre := fun stx self => do
      if Parser.isTerminalCommand stx then pure none else
        let count := self.count + 10
        let some readi := emitter.readIntermediate | return none
        return some <| .node "ii" count [readi])
    (post := fun _ self preState =>
      pure { count := (preState.map (·.getCount)).getD self.count })

initialize emitter'' : StatefulLinter Counter Tree ←
  registerStatefulLinterErgo (Counter.mk 0)
    (pre := fun stx self => do
      if Parser.isTerminalCommand stx then pure none else
        let count := self.count + 100
        let some readi := emitter.readIntermediate | return none
        let some readii := emitter'.readIntermediate | return none
        return some <| .node "iii" count [readii, readi])
    (post := fun _ self preState =>
      pure { count := (preState.map (·.getCount)).getD self.count })

initialize
  registerReader emitter "reader A(i)"
  registerReader emitter "reader B(i)"
  registerReader emitter "reader C(i)"
  registerReader emitter' "reader A(ii)"
  registerReader emitter' "reader B(ii)"
  registerReader emitter' "reader C(ii)"
  registerReader emitter'' "reader A(iii)"
  registerReader emitter'' "reader B(iii)"
  registerReader emitter'' "reader C(iii)"

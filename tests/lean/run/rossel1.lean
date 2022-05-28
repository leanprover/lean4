constant ID : Type

-- A `Reactor` contains "things" identified by an `ID`. It also contains other `Reactor`s, thereby giving us a tree structure of reactors.
inductive Reactor
  | mk
    (things : ID → Option Nat)
    (nested : ID → Option Reactor)

-- Structure projections.
def Reactor.things : Reactor → ID → Option Nat     | mk t _ => t
def Reactor.nested : Reactor → ID → Option Reactor | mk _ n => n

inductive Lineage : Reactor → ID → Type
  | thing {rtr i} : (∃ t, rtr.things i = some t) → Lineage rtr i
  | nested {rtr' i' rtr i} : (Lineage rtr' i) → (rtr.nested i' = some rtr') → Lineage rtr i

def Lineage.container' {rtr i} : Lineage rtr i → (Option ID × Reactor)
  | .nested (.nested l h) _ => (Lineage.nested l h).container'
  | @nested rtr' i' .. => (i', rtr')
  | _ => (none, rtr)

attribute [simp] Lineage.container'

#check @Lineage.container'._eq_1
#check @Lineage.container'._eq_2
#check @Lineage.container'._eq_3

@[simp] def Lineage.container : Lineage rtr i → (Option ID × Reactor)
  | nested l@h:(nested ..) _ => l.container
  | @nested rtr' i' .. => (i', rtr')
  | _ => (none, rtr)

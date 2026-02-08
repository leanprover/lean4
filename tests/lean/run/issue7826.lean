axiom SparseSet : Nat → Type

def SparseSet.insert {n} (set : SparseSet n) (v : Fin n) : SparseSet n := sorry

inductive Node where
  | epsilon (next : Nat)

structure NFA where
  nodes : Array Node

def NFA.get (nfa : NFA) (i : Nat) (h : i < nfa.nodes.size) : Node :=
  nfa.nodes[i]

structure Strategy' where
  T : Type

-- set_option trace.Meta.appBuilder true
-- set_option trace.Meta.isDefEq true

def εClosure (σ : Strategy') (nfa : NFA) (states : SparseSet nfa.nodes.size) (stack : List (Fin nfa.nodes.size)) :
  -- REPRO: using `σ.T` is necessary to reproduce.
  Option σ.T :=
  match stack with
  | [] => .none
  | state :: stack' =>
    -- REPRO: removing this `if` fixes the error.
    if true then
      εClosure σ nfa states stack'
    else
      -- REPRO: this insert is necessary to reproduce.
      let states' := states.insert state
      match nfa.get state state.isLt with
      | .epsilon state' =>
        -- REPRO: this line is also necessary to reproduce.
        have isLt : state' < nfa.nodes.size := sorry
        sorry
-- REPRO: using well-founded recursion is necessary to reproduce.
-- NOTE: the original code uses well-founded recursion to take visited states (`states`) into account.
termination_by /-structural-/ stack

module

/-! Proposition fixtures, including rejected axiom and placeholder dependencies. -/

public section

def Accepted.first : Prop := forall n : Nat, n + n = 2 * n
def Accepted.second : Prop := forall n : Nat, n + 0 = n
def Accepted.unused : Prop := True
def Accepted.notAProp : Nat := 1
def Accepted.parameterized (n : Nat) : Prop := n = n
universe u
def Accepted.polymorphic : Prop := forall a : Sort u, a = a
axiom unapproved : Nat
def Accepted.withAxiom : Prop := unapproved = unapproved
def Accepted.withSorry : Prop := by sorry

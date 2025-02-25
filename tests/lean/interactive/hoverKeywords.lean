/-!
This file tests that hovers for various kinds of declarations include the correct keywords, both in
the declarations themselves and in use sites.

For example, hovering `X` in the following code should show the signature `class X (α : Type) : Type`:
````
class X (α : Type) where
  get : Nat → α
````


The following combinations are tested:
1. Declaration and use sites
2. Declaration types structure, class, inductive, class inductive, def, theorem, axiom, opaque
3. In and out of namespaces
4. Private and non-private

In each case, the correct fully-qualified name and keyword are shown.
-/

structure C : Type where
        --^ textDocument/hover

structure C' : Type extends C where
        --^ textDocument/hover
                          --^ textDocument/hover
  foo ::

private structure D : Type extends C' where
                --^ textDocument/hover
                                 --^ textDocument/hover
  x : Nat

namespace NS

structure C : Type where
        --^ textDocument/hover

structure C' : Type extends C where
        --^ textDocument/hover
                          --^ textDocument/hover
  foo ::

private structure D : Type extends C' where
                --^ textDocument/hover
                                 --^ textDocument/hover
  x : Nat

end NS


class Cl (α : Type) : Type where
    --^ textDocument/hover
  x : α

class Cl' (α : Type) : Type extends Cl Nat where
    --^ textDocument/hover
                                  --^ textDocument/hover
  y : α

private class Cl'' (α : Type) : Type extends Cl Nat where
             --^ textDocument/hover
                                           --^ textDocument/hover

namespace NS.NS

class Cl (α : Type) : Type where
    --^ textDocument/hover
  x : α

class Cl' (α : Type) : Type extends Cl Nat where
    --^ textDocument/hover
                                  --^ textDocument/hover
  y : α

private class Cl'' (α : Type) : Type extends Cl Nat where
            --^ textDocument/hover
                                           --^ textDocument/hover

end NS.NS

inductive A where
        --^ textDocument/hover
  | x

private inductive A' where
                --^ textDocument/hover
  | x

namespace NS

inductive A where
        --^ textDocument/hover
  | x

private inductive A' where
                --^ textDocument/hover
  | x

end NS

class inductive B where
              --^ textDocument/hover
  | x

private class inductive B' where
                      --^ textDocument/hover
  | x

instance instB : B := .x
          --^ textDocument/hover

example := instB
           --^ textDocument/hover

private instance instB' : B := .x
                  --^ textDocument/hover

namespace NS

class inductive B where
              --^ textDocument/hover
  | x

private class inductive B' where
                      --^ textDocument/hover
  | x

end NS

def x : Nat := 44
  --^ textDocument/hover
def y : Nat := x
             --^ textDocument/hover
  --^ textDocument/hover

theorem x_eq_44 : x = 44 := by rfl
          --^ textDocument/hover
                --^ textDocument/hover

theorem y_eq_44 : y = 44 := by simp [y, x_eq_44]
          --^ textDocument/hover
                --^ textDocument/hover
                                      --^ textDocument/hover

axiom yes : True
    --^ textDocument/hover
theorem ok : True := yes
      --^ textDocument/hover
                   --^ textDocument/hover

private axiom indeed : True
              --^ textDocument/hover

opaque yes' : True
     --^ textDocument/hover
def yes'' : True := have := indeed; yes'
   --^ textDocument/hover
                          --^ textDocument/hover
                                   --^ textDocument/hover

namespace NS'

def x : Nat := 44
  --^ textDocument/hover
def y : Nat := x
             --^ textDocument/hover
  --^ textDocument/hover

theorem x_eq_44 : x = 44 := by rfl
          --^ textDocument/hover
                --^ textDocument/hover

theorem y_eq_44 : y = 44 := by simp [y, x_eq_44]
          --^ textDocument/hover
                --^ textDocument/hover
                                      --^ textDocument/hover

axiom yes : True
    --^ textDocument/hover
theorem ok : True := yes
      --^ textDocument/hover
                   --^ textDocument/hover

private axiom indeed : True
              --^ textDocument/hover

opaque yes' : True
     --^ textDocument/hover
def yes'' : True := have := indeed; yes'
   --^ textDocument/hover
                          --^ textDocument/hover
                                   --^ textDocument/hover

def yay := "yay"

end NS'

namespace Other

open NS'

example := yay
           --^ textDocument/hover
end Other


declare_syntax_cat c
                 --^ textDocument/hover
syntax "C" : c
           --^ textDocument/hover
  --^ textDocument/hover

syntax (name := cD) "D" : c
               --^ textDocument/hover
                        --^ textDocument/hover
syntax "⟪" c "⟫" : term
         --^ textDocument/hover
                  --^ textDocument/hover


abbrev Abb := "Abb"
     --^ textDocument/hover

example := Abb
         --^ textDocument/hover

def Abb' := "Abb"
    --^ textDocument/hover

example := Abb'
         --^ textDocument/hover

attribute [reducible] Abb'
                     --^ textDocument/hover

example := Abb'
         --^ textDocument/hover

namespace NS

private abbrev Abb := "Abb"
             --^ textDocument/hover

example := Abb
         --^ textDocument/hover

private def Abb' := "Abb"
          --^ textDocument/hover

example := Abb'
         --^ textDocument/hover

attribute [reducible] Abb'
                     --^ textDocument/hover

example := Abb'
          --^ textDocument/hover
end NS

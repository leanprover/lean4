/-!
Here we test that lean correctly complains if `termination_by` has too many variables,
and that it does the right thing if it has fewer variables.
-/

opaque dec1 : Nat → Nat
axiom dec1_lt (n : Nat) : dec1 n < n
opaque dec2 : Nat → Nat
axiom dec2_lt (n : Nat) : dec2 n < n

namespace Basic

def tooManyVars (n : Nat) : Nat := tooManyVars (dec1 n)
  termination_by x => x -- Error
  decreasing_by apply dec1_lt

def okVariables1 (n : Nat) : Nat := okVariables1 (dec1 n)
  termination_by n
  decreasing_by apply dec1_lt


def blankArrow (n : Nat) : Nat := blankArrow (dec1 n)
  termination_by => x -- Error
  decreasing_by apply dec1_lt

def fewerVariables1 (n : Nat) : Nat → Nat → Nat := fun a b => fewerVariables1 (dec2 n) a (dec1 b)
  termination_by n -- Not an error
  decreasing_by apply dec2_lt

def fewerVariables2 (n : Nat) : Nat → Nat → Nat := fun a b => fewerVariables2 n (dec1 a) (dec2 b)
  termination_by a => a
  decreasing_by apply dec1_lt -- NB: dec2_lt would no work

def okVariables2 (n : Nat) : Nat → Nat → Nat := fun a b => okVariables2 n (dec1 a) (dec2 b)
  termination_by a b => b
  decreasing_by apply dec2_lt

def tooManyVariables2 (n : Nat) : Nat → Nat → Nat := fun a b => tooManyVariables2 n (dec1 a) (dec2 b)
  termination_by a b c => b
  decreasing_by apply dec1_lt

end Basic

namespace WithVariable

variable (v : Nat)

def tooManyVars (n : Nat) : Nat := tooManyVars (dec1 n) + v
  termination_by x => x -- Error
  decreasing_by apply dec1_lt

def okVariables1 (n : Nat) : Nat := okVariables1 (dec1 n) + v
  termination_by n
  decreasing_by apply dec1_lt


def blankArrow (n : Nat) : Nat := blankArrow (dec1 n) + v
  termination_by => x -- Error
  decreasing_by apply dec1_lt

def fewerVariables1 (n : Nat) : Nat → Nat → Nat := fun a b =>
    fewerVariables1 (dec2 n) a (dec1 b) + v
  termination_by n
  decreasing_by apply dec2_lt

def fewerVariables2 (n : Nat) : Nat → Nat → Nat := fun a b =>
    fewerVariables2 n (dec1 a) (dec2 b) + v
  termination_by a => a
  decreasing_by apply dec1_lt

def okVariables2 (n : Nat) : Nat → Nat → Nat := fun a b =>
    okVariables2 n a (dec1 b) + v
  termination_by a b => b
  decreasing_by apply dec1_lt

end WithVariable

namespace InLetRec

def foo1 (v : Nat) := 5
  where
  tooManyVars (n : Nat) : Nat := tooManyVars (dec1 n) + v
    termination_by x => x -- Error
    decreasing_by apply dec1_lt

def foo2 (v : Nat) := 5
  where
  okVariables1 (n : Nat) : Nat := okVariables1 (dec1 n) + v
    termination_by n
    decreasing_by apply dec1_lt

def foo3 (v : Nat) := 5
  where
  blankArrow (n : Nat) : Nat := blankArrow (dec1 n) + v
    termination_by => x -- Error
    decreasing_by apply dec1_lt

def foo4 (v : Nat) := 5
  where
  fewerVariables1 (n : Nat) : Nat → Nat → Nat := fun a b =>
      fewerVariables1 (dec2 n) a (dec1 b) + v
    termination_by n
    decreasing_by apply dec2_lt

def foo5 (v : Nat) := 5
  where
  fewerVariables2 (n : Nat) : Nat → Nat → Nat := fun a b =>
      fewerVariables2 n (dec1 a) (dec2 b) + v
    termination_by a => a
    decreasing_by apply dec1_lt

def foo6 (v : Nat) := 5
  where
  okVariables2 (n : Nat) : Nat → Nat → Nat := fun a b =>
      okVariables2 n a (dec1 b) + v
    termination_by a b => b
    decreasing_by apply dec1_lt

end InLetRec

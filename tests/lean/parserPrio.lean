--

-- New notation that overlaps with existing notation
syntax (name := myPair) (priority := high) "(" term "," term ")" : term

macro_rules (kind := myPair)
| `(($a, $b)) => `([$a, $b])

#eval (1, 2) -- not ambiguous since myPair parser has higher priority

theorem ex1 : (1, 2) = [1, 2] :=
rfl

-- Define macro for expanding the builtin triple notation
-- Macros bypass builtin elaboration functions
macro_rules
| `(($a, $b, $c)) => `($a + $b + $c)

#eval (1, 2, 3)

syntax (name := mySingleton) "[" term "]" : term

macro_rules (kind := mySingleton)
| `([$a]) => `(2 * $a)

-- TODO: "ambiguous, possible interpretations" error messages print with
-- a lot of detail since most mvars have not been resolved yet
#check [1] -- ambiguous it can be `mySingleton` or the singleton list


syntax (priority := 100) "(" term "," term ", " term ")" : term -- priority without a kind

macro_rules
| `(($a, $b, $c)) => `([$a, $b, $c])

#eval (1,2,3)

theorem ex2 : (1, 2, 3) = [1, 2, 3] :=
rfl

theorem ex3 : (1, 2, 3, 4) = Prod.mk 1 (Prod.mk 2 (Prod.mk 3 4)) :=
rfl

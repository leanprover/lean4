set_option showInferredTerminationBy true

def countUp (n i acc : Nat) : Nat :=
  if i < n then
    countUp n (i+1) (acc + i)
  else
    acc

def all42 (xs : Array Nat) (i : Nat) : Bool :=
  if h : i < xs.size then
    if xs[i] = 42 then
      all42 xs (i+1)
    else
      false
  else
    true

def henrik1 (xs : Array Nat) (i : Nat) : Bool :=
  if h : i < xs.size then
    if xs[i] = 42 then
      henrik1 (xs.push 42) (i+2)
    else
      false
  else
    true

def merge (xs ys : Array Nat) : Array Nat :=
  let rec loop (i j : Nat) (acc : Array Nat) : Array Nat :=
    if _ : i < xs.size then
      if _ : j < ys.size then
        if xs[i] < ys[j] then
          loop (i+1) j (acc.push xs[i])
        else
          loop i (j+1) (acc.push ys[j])
      else
        loop (i+1) j (acc.push xs[i])
    else
      if _ : j < ys.size then
        loop i (j+1) (acc.push ys[j])
      else
        acc
  loop 0 0 #[]

def distinct (xs : Array Nat) : Bool :=
  let rec loop (i j : Nat) : Bool :=
    if _ : i < xs.size then
      if _ : j < i then
        if xs[j] = xs[i] then
          false
        else
          loop i (j+1)
      else
        loop (i+1) 0
    else
      true
  loop 0 0

-- This examples shows a limitation of our current `decreasing_tactic`.
-- Guesslex infers `termination_by (Array.size xs - i, i)` but because `decreasing_with` is using
--     repeat (first | apply Prod.Lex.right | apply Prod.Lex.left)
-- it cannot solve this goal. But if we leave the Prod.Lex-handling to omega, it works.
-- See https://github.com/leanprover/lean4/issues/3906
def weird (xs : Array Nat) (i : Nat) : Bool :=
  if _ : i < xs.size then
    if _ : 0 < i then
      if xs[i] = 42 then
        weird xs.pop (i - 1)
      else
        weird xs (i+1)
    else
      weird xs (i+1)
  else
    true
decreasing_by all_goals (try simp only [Array.size_pop]); omega


/--
This checks
* the presentation of complex measures in the table
* that multiple recursive calls do not lead to the same argument tried multiple times.
* it uses `e` instead of `e - 0`
* that we do not get measures from refined arguments
-/
def failure (xs : Array Nat) (i : Nat) : Bool :=
  if h : i < xs.size then failure xs i && failure xs i && failure xs (i + 1) else
  if h : i + 1 < xs.size then failure xs i else
  let j := i
  if h : j < xs.size then failure xs (j+1) else
  if h : 0 < i then failure xs (j+1) else
  if h : 42 < i then failure xs (j+1) else
  if h : xs.size < i then failure xs (j+1) else
  if h : 42 < i + i then failure xs (j+1) else
  match i with
  | 0 => true
  | i+1 =>
      if h : i < xs.size + 5 then
        failure xs i
      else
        false

mutual
def mutual_failure (xs : Array Nat) (i : Nat) : Bool :=
  if h : i < xs.size then
    mutual_failure2 xs i && mutual_failure2 xs i && mutual_failure2 xs (i + 1)
  else
  if h : i + 1 < xs.size then
    mutual_failure2 xs i
  else
  let j := i
  if h : j < xs.size then
    mutual_failure2 xs (j+1)
  else
  match i with
  | 0 => true
  | i+1 =>
      if h : i < xs.size then
        mutual_failure2 xs i
      else
        false

def mutual_failure2 (xs : Array Nat) (i : Nat) : Bool :=
  if h : i < xs.size then
    mutual_failure xs i && mutual_failure xs i && mutual_failure xs (i + 1)
  else
  let j := i
  if h : j < xs.size then
    mutual_failure xs (j+1)
  else
  match i with
  | 0 => true
  | i+1 =>
      if h : i < xs.size then
        mutual_failure xs i
      else
        false
end

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

/--
This checks
* the presentation of complex measures in the table
* that multiple recursive calls do not lead to the same argument tried multiple times.
* that we do not get measures from refined arguments
-/
def failure (xs : Array Nat) (i : Nat) : Bool :=
  if h : i < xs.size then
    failure xs i && failure xs i && failure xs (i + 1)
  else
  if h : i + 1 < xs.size then
    failure xs i
  else
  let j := i
  if h : j < xs.size then
    failure xs (j+1)
  else
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

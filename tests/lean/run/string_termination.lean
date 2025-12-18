module

-- Test that termination proofs for stepping through a string with `next` and `prev` works.

def isConsonant (i : String.Pos str) : Bool :=
  match i.get! with
  | 'a' | 'e' | 'i' | 'o' | 'u' => false
  | 'y' =>
    if h : i = str.startPos then true
    else !isConsonant (i.prev h)
  | _ => true
termination_by i.down

def measure₁ (word : String) : Nat :=
  let rec aux (pos : String.Pos word) (inVowel : Bool) (count : Nat) : Nat :=
    match h : pos.next? with
    | some next =>
      if !isConsonant pos then
        aux next true count
      else if inVowel then
        aux next false (count + 1)
      else
        aux next false count
    | none => count
  termination_by pos

  aux word.startPos false 0

def measure₂ (word : String) : Nat :=
  let rec aux (pos : String.Pos word) (inVowel : Bool) (count : Nat) : Nat :=
    if h : pos = word.endPos then count
    else
      let next := pos.next h
      if !isConsonant pos then
        aux next true count
      else if inVowel then
        aux next false (count + 1)
      else
        aux next false count
  termination_by pos

  aux word.startPos false 0

-- The following two snippets causes Lean to throw error:

def areAllSame' (arr : Array Nat) (i : Nat := 0) :=
  if _ : i < arr.size then
    if arr[i] = arr[0] then
      areAllSame' arr (i + 1)
    else
      false
  else
    true

def areAllSame2' (arr : Array Nat) (i : Nat := 0) (j : Nat) :=
  if _ : i < arr.size then
    if arr[i] = arr[0] then
      areAllSame2' arr (i + 1) (j + 1)
    else
      false
  else
    true

--Removing the optional argument works

def areAllSame (arr : Array Nat) (i : Nat) :=
  if _ : i < arr.size then
    if arr[i] = arr[0] then
      areAllSame arr (i + 1)
    else
      false
  else
    true

def areAllSame2 (arr : Array Nat) (i : Nat) (j : Nat) :=
  if _ : i < arr.size then
    if arr[i] = arr[0] then
      areAllSame2 arr (i + 1) (j + 1)
    else
      false
  else
    true

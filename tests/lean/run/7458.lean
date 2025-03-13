-- set_option trace.Elab.definition.structural true
-- set_option trace.Elab.definition.scc true
-- set_option trace.Elab.definition.wf true
-- set_option trace.Elab.definition true
-- set_option trace.Elab.definition true
-- The following snippet causes Lean to throw error:

def areAllSame' (arr : Array Nat) (i : Nat := 0) :=
  if _ : i < arr.size then
    if arr[i] = arr[0] then
      areAllSame' arr (i + 1)
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

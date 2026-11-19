def computeMaxDepth (s : String.Slice) : Int := Id.run do
  let mut depth : Int := 0
  let mut maxDepth : Int := 0
  for c in s do
    if c == '(' then
      depth := depth + 1
      maxDepth := max maxDepth depth
    else if c == ')' then
      depth := depth - 1
      maxDepth := max maxDepth depth
  return maxDepth

def parseNestedParens (parenString : String.Slice) : Array Int :=
  (parenString.split ' ').map computeMaxDepth |>.toArray

example : parseNestedParens "() () () ()" = #[1, 1, 1, 1] := by cbv
example : parseNestedParens "() (())" = #[1, 2] := by cbv

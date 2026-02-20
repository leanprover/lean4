example: p ∧ q := by first | apply And.intro <;> fail | sorry

variable (p q : Prop)

example (hp : p) : p := by
  try trivial -- succeeds, as expected

example : p := by
  try trivial -- fails quietly, as expected
  admit

example (hp : p) (hq : q) : p ∧ q := by
  try trivial -- succeeds, as expected

example (hp : p) : p ∧ q := by
  try trivial
  admit

example (hq : p) : p ∧ q := by
  try trivial
  admit

example : p ∧ q := by
  try trivial -- fails quietly
  admit       -- splits goals p and q

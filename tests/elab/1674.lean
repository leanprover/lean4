inductive T : Prop where
  | nil (n: Nat)
  | fn (f: Nat → T)

def inc: T → T
  | T.nil n => T.nil (n+1)
  | T.fn f => T.fn fun n => inc (f n)

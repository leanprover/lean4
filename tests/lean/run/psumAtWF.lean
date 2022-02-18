mutual

def fn (f : α → α) (a : α) (n : Nat) : α :=
  match n with
  | 0 => a
  | n+1 => gn f (f (f a)) (f a) n

def gn (f : α → α) (a b : α) (n : Nat) : α :=
  match n with
  | 0 => b
  | n+1 => fn f (f b) n

end
termination_by
  fn n => n
  gn n => n

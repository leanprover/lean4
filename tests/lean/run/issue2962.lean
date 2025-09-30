inductive N where
  | zero : N
  | succ : N → N

def replace (f : N → Option N) (t : N) : N :=
  match f t with
  | some u => u
  | none =>
    match t with
    | .zero => .zero
    | .succ t' => replace f t'

/--
info: equations:
@[defeq] theorem replace.eq_1 : ∀ (f : N → Option N),
  replace f N.zero =
    match f N.zero with
    | some u => u
    | none => N.zero
@[defeq] theorem replace.eq_2 : ∀ (f : N → Option N) (t' : N),
  replace f t'.succ =
    match f t'.succ with
    | some u => u
    | none => replace f t'
-/
#guard_msgs in
#print equations replace

def replace2 (f : N → Option N) (t1 t2 : N) : N :=
  match f t1 with
  | some u => u
  | none =>
    match t2 with
    | .zero => .zero
    | .succ t' => replace2 f t1 t'

/--
info: equations:
@[defeq] theorem replace2.eq_1 : ∀ (f : N → Option N) (t1 : N),
  replace2 f t1 N.zero =
    match f t1 with
    | some u => u
    | none => N.zero
@[defeq] theorem replace2.eq_2 : ∀ (f : N → Option N) (t1 t' : N),
  replace2 f t1 t'.succ =
    match f t1 with
    | some u => u
    | none => replace2 f t1 t'
-/
#guard_msgs in
#print equations replace2

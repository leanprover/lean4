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


-- Now also mutual

mutual
inductive N1 where
  | zero : N1
  | succ : N2 → N1
inductive N2 where
  | zero : N2
  | succ : N1 → N2
end

mutual
def replaceMut1 (f : N1 → Option N1) (g : N2 → Option N2) (t : N1) : N1 :=
  match f t with
  | some u => u
  | none =>
    match t with
    | .zero => .zero
    | .succ t' => .succ (replaceMut2 f g t')
def replaceMut2 (f : N1 → Option N1) (g : N2 → Option N2) (t : N2) : N2 :=
  match g t with
  | some u => u
  | none =>
    match t with
    | .zero => .zero
    | .succ t' => .succ (replaceMut1 f g t')
end

/--
info: theorem replaceMut1.eq_def : ∀ (f : N1 → Option N1) (g : N2 → Option N2) (t : N1),
  replaceMut1 f g t =
    match f t with
    | some u => u
    | none =>
      match t with
      | N1.zero => N1.zero
      | N1.succ t' => N1.succ (replaceMut2 f g t')
-/
#guard_msgs in
#print sig replaceMut1.eq_def
/--
info: theorem replaceMut2.eq_def : ∀ (f : N1 → Option N1) (g : N2 → Option N2) (t : N2),
  replaceMut2 f g t =
    match g t with
    | some u => u
    | none =>
      match t with
      | N2.zero => N2.zero
      | N2.succ t' => N2.succ (replaceMut1 f g t')
-/
#guard_msgs in
#print sig replaceMut2.eq_def

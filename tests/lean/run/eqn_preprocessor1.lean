open nat

inductive Vec (A : Type) : nat → Type
| nil {} : Vec 0
| cons   : Π {n}, A → Vec n → Vec (succ n)

open Vec

def append1 {A : Type} : Π {m n : nat}, Vec A m -> Vec A n -> Vec A (n + m)
| _ m nil         ys := ys
| _ m (cons x xs) ys := cons x (append1 xs ys)

def append2 {A : Type} : Π {m n : nat}, Vec A m -> Vec A n -> Vec A (n + m)
| _ _ nil         ys := ys
| _ _ (cons x xs) ys := cons x (append2 xs ys)

def append3 {A : Type} : Π {m n : nat}, Vec A m -> Vec A n -> Vec A (n + m)
| ._ m nil         ys := ys
| ._ m (cons x xs) ys := cons x (append1 xs ys)


inductive Fin : nat → Type
| fzero : Π {n}, Fin (nat.succ n)

open Fin

def fmin1 : Π {n : nat} (x y : Fin n),  Fin n
| ._ fzero fzero := fzero

def fmin2 : Π {n : nat} (x y : Fin n),  Fin n
| _ fzero fzero := fzero

def fmin3 : Π {n : nat} (x y : Fin n),  Fin n
| n fzero fzero := fzero

def fmin4 : Π {n : nat} (x y : Fin n),  Fin n
| .(succ n) (@fzero n) (@fzero .(n)) := fzero

def fmin5 : Π {n : nat} (x y : Fin n),  Fin n
| .(succ n) (@fzero .(n)) (@fzero n) := fzero

def fmin6 : Π {n : nat} (x y : Fin n),  Fin n
| .(succ _) fzero fzero := fzero

example (n : nat) (x y : Fin n) : fmin1 x y = fmin2 x y :=
begin cases x, cases y, refl end

example (n : nat) (x y : Fin n) : fmin1 x y = fmin3 x y :=
begin cases x, cases y, refl end

example (n : nat) (x y : Fin n) : fmin1 x y = fmin4 x y :=
begin cases x, cases y, refl end

example (n : nat) (x y : Fin n) : fmin1 x y = fmin5 x y :=
begin cases x, cases y, refl end

example (n : nat) (x y : Fin n) : fmin1 x y = fmin6 x y :=
begin cases x, cases y, refl end

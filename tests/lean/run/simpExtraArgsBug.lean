variable {X : Type u} {Y : Type v} {Z : Type w}

def comp (f : Y→Z) (g : X→Y) (x : X) := f (g x)
def swap (f : X→Y→Z) (y : Y) (x : X) := f x y
def diag (f : X→X→Y) (x : X) := (f x x)

@[simp] def comp_reduce (f : Y→Z) (g : X→Y) (x : X) : (comp f g x) = f (g x) := by simp[comp] done
def swap_reduce (f : X→Y→Z) (y : Y) (x : X) : (swap f y x) = f x y := by simp[swap] done
@[simp] def diag_reduce (f : X→X→Y) (x : X) : (diag f x) = f x x := by simp[diag] done

def subs : (X→Y→Z) → (X→Y) → (X→Z) := (swap (comp (comp diag) (comp comp (swap comp))))


def foo {W} := ((comp comp (swap comp)) : (X→Y) → _ → W → X → Z)

def subs_reduce' (f : X→Y→Z) (g : X→Y) (x : X) : comp (comp diag) foo g f x = (f x) (g x) :=
by
  simp
  simp [foo, swap, comp]

def subs_reduce'' (f : X→Y→Z) (g : X→Y) (x : X) : comp (comp diag) foo g f x = (f x) (g x) :=
by
  simp
  admit

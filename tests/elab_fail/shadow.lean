import Lean



theorem ex1 {α} (x : α) (h : x = x) (x : α) : x = x :=
h

set_option pp.sanitizeNames false in
theorem ex2 {α} (x : α) (h : x = x) (x : α) : x = x :=
h -- this error is confusing because we have disabled `pp.sanitizeNames`

def foo1 {α} [Inhabited α] (inst inst : α) : {β δ : Type} → α → β → δ → α × β × δ :=
_

set_option pp.sanitizeNames false in
def foo2 {α} [Inhabited α] (inst inst : α) : {β δ : Type} → α → β → δ → α × β × δ :=
_

def foo3 {α β} (inst : α) (inst : β) (b : β) (inst : α) [Inhabited α] : {β δ : Type} → α → β → δ → α × β × δ :=
_

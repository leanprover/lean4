new_frontend

theorem ex1 {α} (x : α) (h : x = x) (x : α) : x = x :=
h

set_option pp.sanitizeNames false in
theorem ex2 {α} (x : α) (h : x = x) (x : α) : x = x :=
h -- this error is confusing because we have disabled `pp.sanitizeNames`

set_option pp.sanitizeNames true in
def foo {α} [Inhabited α] (inst inst : α) : {β δ : Type} → α → β → δ → α × β × δ :=
_

set_option pp.sanitizeNames false in
def foo {α} [Inhabited α] (inst inst : α) : {β δ : Type} → α → β → δ → α × β × δ :=
_

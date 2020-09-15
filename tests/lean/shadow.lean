new_frontend

theorem ex1 {α} (x : α) (h : x = x) (x : α) : x = x :=
h

set_option pp.sanitizeNames false

theorem ex2 {α} (x : α) (h : x = x) (x : α) : x = x :=
h -- this error is confusing because we have disabled `pp.sanitizeNames`

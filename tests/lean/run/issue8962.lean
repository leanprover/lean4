-- This triggered a bug in the linear-size `noConfusionType` construction
-- which confused the kernel when producing the `noConfusion` lemma.

-- set_option debug.skipKernelTC true
set_option pp.universes true

-- Works

inductive S where
| a {α : Sort u} {β : Type v} (f : α → β)
| b

-- Didn't work

inductive T where
| a {α : Sort u} {β : Sort v} (f : α → β)
| b

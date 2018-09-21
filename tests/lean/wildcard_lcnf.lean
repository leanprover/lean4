inductive term
| var   : nat → term
| const : string → term
| app   : term → term → term


set_option pp.binder_types false
set_option pp.compact_let true
set_option trace.compiler.lcnf true

def app_of : term → term
| (term.app f a) := app_of f
| e              := e

def is_app : term → option term
| r@(term.app f a) := some r
| _                := none

def bin_fn : term → term
| (term.app (term.app f a1) a2) := f
| e                             := e

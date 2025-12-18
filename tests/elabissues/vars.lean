def f1 {α} [ToString α] (a : α) : String := -- works
">> " ++ toString a

-- Moving `{α} [ToString α]` to a `variables` break the example
variable {α} [ToString α]
def f2 (a : α) : String :=
">> " ++ toString a

class Dummy (α : Type) := (val : α)

/- The following fails because `variables {α : Type _} [Dummy α]` is processed as `variable {α : Type _} variable [Dummy α]`
   The first command elaborates `α` as `variable {α : Type u_1}` where `u_1` is a fresh metavariable.
   That is, in Lean3, metavariables are resolved before the end of the command. -/
variable {α : Type _} [Dummy α]

def f3 {α : Type _} [Dummy α] : α := -- works
Dummy.val α

/-
In Lean4, we should use a different approach. We keep a metavariable context in the command elaborator.
Before, a declaration `D` is sent to the kernel we resolve the metavariables occurring in `D`.
We must implement a MetavarContext GC to make sure the metavariable context does not keep increasing.
That is, after a declaration is sent to the kernel, we visit all variables in the elaborator context and
instantiate assigned metavariables. Then, we delete all assigned metavariables.
-/

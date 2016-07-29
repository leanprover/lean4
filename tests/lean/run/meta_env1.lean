open list

meta_definition e := environment.mk_std 0

vm_eval environment.trust_lvl e
vm_eval environment.is_std e

vm_eval (environment.add e (declaration.def `foo []
                                           (expr.sort (level.succ (level.zero)))
                                           (expr.sort (level.succ (level.zero)))
                                           bool.tt) : exceptional environment)

meta_definition e1 := (environment.add e (declaration.def `foo []
                                            (expr.sort (level.succ (level.zero)))
                                            (expr.sort level.zero)
                                            bool.tt) : exceptional environment)

print "-----------"
open name

vm_eval do
   e₁ ← environment.add e (declaration.def `foo []
                                           (expr.sort (level.succ (level.zero)))
                                           (expr.sort level.zero)
                                           bool.tt),
   e₂ ← environment.add_inductive e₁ `Two [] 0 (expr.sort (level.succ level.zero))
                                  [(`Zero, expr.const `Two []),
                                   (`One,  expr.const `Two [])],
   d₁ ← environment.get e₂ `Zero,
   d₂ ← environment.get e₂ `foo,
   /- TODO(leo): use

        return (declaration.type d)

      We currently don't use 'return' because the type is too high-order.

        return : ∀ {m : Type → Type} [monad m] {A : Type}, A → m A
      It is the kind of example where we should fallback to first-order unification for
      inferring the (m : Type → Type)

      The new elaborator should be able to handle it.
   -/
   exceptional.success (declaration.type d₁, declaration.type d₂,
                        environment.is_recursor e₂ `Two.rec,
                        environment.constructors_of e₂ `Two,
                        environment.fold e₂ (to_format "") (λ d r, r ++ format.line ++ to_fmt (declaration.to_name d)))

namespace coercion_with_no_args

constants (P Q : Prop) (f : P → Q) (p : P)
attribute f [coercion]

eval f p

end coercion_with_no_args

namespace coercion_with_arg

constants (P Q : true → Prop) (f : ∀ {t}, P t → Q t) (p : P trivial)
attribute f [coercion]

eval f p

end coercion_with_arg

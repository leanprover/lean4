set_option pp.all true

open tactic

#tactic (∀ (p : Prop), p → p),
 do env ← get_env,
    return unit.star

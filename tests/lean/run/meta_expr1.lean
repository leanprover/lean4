open unsigned list

meta definition e1  := expr.app (expr.app (expr.const `f []) (expr.mk_var 1)) (expr.const `a [])
meta definition e1' := expr.app (expr.app (expr.const `f []) (expr.mk_var 1)) (expr.const `a [])

meta definition tst : e1 = e1' :=
rfl

#eval e1

#eval expr.fold e1 (0:nat) (λ e d n, n+1)

meta definition l1 := expr.lam `a binder_info.default (expr.sort level.zero) (expr.mk_var 0)
meta definition l2 := expr.lam `b binder_info.default (expr.sort level.zero) (expr.mk_var 0)
meta definition l3 := expr.lam `a binder_info.default (expr.const `nat []) (expr.mk_var 0)

#eval l1
#eval l2
#eval l3
#eval decidable.to_bool (l1 = l2)
#eval decidable.to_bool (l1 =ₐ l2)

#eval expr.lex_lt (expr.const `a []) (expr.const `b [])
#eval expr.lt (expr.const `a []) (expr.const `b [])

meta definition v1 := expr.app (expr.app (expr.const `f []) (expr.mk_var 0)) (expr.mk_var 1)

#eval v1
#eval expr.instantiate_var v1 (expr.const `a [])

#eval expr.instantiate_vars v1 [expr.const `a [], expr.const `b []]

meta definition fv1 : expr :=
expr.app
  (expr.app (expr.const `f [])
            (expr.local_const `a `a binder_info.default (expr.sort level.zero)))
  (expr.local_const `b `b binder_info.default (expr.sort level.zero))

#eval fv1

#eval expr.abstract_local (expr.abstract_local fv1 `a) `b
#eval expr.abstract_locals fv1 [`a, `b]
#eval expr.abstract_locals fv1 [`b, `a]
#eval expr.lift_vars (expr.abstract_locals fv1 [`b, `a]) 1 1
#eval expr.has_local fv1
#eval expr.has_var fv1
#eval expr.has_var (expr.abstract_locals fv1 [`b, `a])

meta definition foo : nat → expr
| 0     := expr.const `aa [level.zero, level.succ level.zero]
| (n+1) := foo n

/-
#eval match foo 10 with
| expr.const n ls := list.head (list.tail ls)
| _               := level.zero
end
-/

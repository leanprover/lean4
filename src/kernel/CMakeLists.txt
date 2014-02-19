add_library(kernel level.cpp diff_cnstrs.cpp expr.cpp expr_eq_fn.cpp
for_each_fn.cpp occurs.cpp replace_fn.cpp free_vars.cpp abstract.cpp
instantiate.cpp context.cpp formatter.cpp max_sharing.cpp kernel_exception.cpp
object.cpp environment.cpp
# normalizer.cpp
# type_checker.cpp kernel.cpp metavar.cpp
# justification.cpp unification_constraint.cpp
# type_checker_justification.cpp pos_info_provider.cpp
# replace_visitor.cpp update_expr.cpp io_state.cpp
# universe_constraints.cpp
)

target_link_libraries(kernel ${LEAN_LIBS})
